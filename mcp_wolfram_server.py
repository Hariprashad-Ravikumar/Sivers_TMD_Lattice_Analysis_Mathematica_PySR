#!/usr/bin/env python3
"""
Wolfram Mathematica MCP Server
--------------------------------
Provides Model Context Protocol (MCP) tools for interacting with a local Wolfram Mathematica Engine.
Enables AI models to:
  - Evaluate Wolfram Language expressions (symbolic algebra, Fourier transforms, integrals, fits)
  - Generate LaTeX representations (TeXForm) for thesis inclusion
  - Render and export publication-quality figures directly to PDF/PNG
  - Extract and read clean code cells from Mathematica .nb files
"""

import os
import sys
import json
import subprocess
import asyncio
from pathlib import Path
from typing import Optional

from mcp.server import MCPServer
from mcp.types import Tool, TextContent

# Default path to WolframKernel on macOS
WOLFRAM_KERNEL_DEFAULT = "/Applications/Mathematica.app/Contents/MacOS/WolframKernel"
WOLFRAM_KERNEL = os.environ.get("WOLFRAM_KERNEL_PATH", WOLFRAM_KERNEL_DEFAULT)

server = MCPServer(
    name="wolfram-mathematica",
    instructions="Tools to execute Wolfram Language code, evaluate symbolic math, export plots, and inspect Mathematica notebooks."
)


def _execute_wolfram_code(code: str, timeout_seconds: int = 120) -> tuple[str, str, int]:
    """Execute raw Wolfram Language code via WolframKernel subprocess."""
    if not os.path.exists(WOLFRAM_KERNEL):
        return "", f"WolframKernel not found at {WOLFRAM_KERNEL}", 1

    # Ensure code terminates with Quit[]
    clean_code = code.strip()
    if not clean_code.endswith("Quit[]") and not clean_code.endswith("Quit[];"):
        clean_code = f"{clean_code}\nQuit[];\n"

    try:
        proc = subprocess.run(
            [WOLFRAM_KERNEL, "-noprompt"],
            input=clean_code.encode("utf-8"),
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=timeout_seconds
        )
        stdout = proc.stdout.decode("utf-8", errors="replace")
        stderr = proc.stderr.decode("utf-8", errors="replace")
        return stdout, stderr, proc.returncode
    except subprocess.TimeoutExpired:
        return "", f"Evaluation timed out after {timeout_seconds} seconds.", 1
    except Exception as e:
        return "", f"Execution error: {str(e)}", 1


@server.tool(
    name="wolfram_eval",
    description="Evaluate arbitrary Wolfram Language (Mathematica) code and return the output."
)
async def wolfram_eval(code: str, timeout_seconds: int = 120) -> str:
    """
    Args:
        code: Wolfram Language code to execute.
        timeout_seconds: Maximum execution time in seconds (default: 120).
    """
    stdout, stderr, code_rc = _execute_wolfram_code(code, timeout_seconds)
    output_parts = []
    if stdout.strip():
        output_parts.append(stdout.strip())
    if stderr.strip():
        output_parts.append(f"Messages/Errors:\n{stderr.strip()}")
    if not output_parts:
        output_parts.append("(Evaluation completed with no output)")
    return "\n\n".join(output_parts)


@server.tool(
    name="wolfram_to_latex",
    description="Evaluate a mathematical expression in Wolfram Language and return its formatted LaTeX (TeXForm) representation."
)
async def wolfram_to_latex(expression: str) -> str:
    """
    Args:
        expression: Wolfram Language expression to evaluate and convert to LaTeX.
    """
    escaped_expr = expression.replace('"', r'\"')
    script = f"""
expr = ToExpression["{escaped_expr}"];
texStr = ToString[TeXForm[expr]];
Print[texStr];
Quit[];
"""
    stdout, stderr, _ = _execute_wolfram_code(script, 30)
    if stderr.strip():
        return f"Error converting to TeXForm: {stderr.strip()}"
    return stdout.strip()


@server.tool(
    name="wolfram_export_plot",
    description="Evaluate Wolfram Language plotting code and export the resulting graphics directly to a file (PDF, PNG, EPS)."
)
async def wolfram_export_plot(plot_code: str, output_path: str, image_format: str = "PDF", resolution: int = 300) -> str:
    """
    Args:
        plot_code: Wolfram Language code that generates a plot or graphics object (e.g. Plot[...], Show[...]).
        output_path: Absolute or relative file path to save the output (e.g. /path/to/thesis/plots/fig1.pdf).
        image_format: Export format: 'PDF', 'PNG', 'EPS', 'SVG' (default: 'PDF').
        resolution: DPI resolution for raster formats (default: 300).
    """
    out_p = Path(output_path).expanduser().resolve()
    out_p.parent.mkdir(parents=True, exist_ok=True)

    script = f"""
UsingFrontEnd[
    plt = {plot_code.strip()};
    res = Export["{str(out_p)}", plt, "{image_format}", ImageResolution -> {resolution}];
    If[FileExistsQ["{str(out_p)}"],
        Print["SUCCESS: Exported to ", "{str(out_p)}", " (Size: ", FileByteCount["{str(out_p)}"], " bytes)"],
        Print["FAILED: Export failed: ", res]
    ];
];
Quit[];
"""
    stdout, stderr, _ = _execute_wolfram_code(script, 60)
    output_parts = []
    if stdout.strip():
        output_parts.append(stdout.strip())
    if stderr.strip():
        output_parts.append(f"Warnings/Messages:\n{stderr.strip()}")
    return "\n\n".join(output_parts)


@server.tool(
    name="read_notebook_cells",
    description="Extract clean, human-readable Wolfram Language input code from a Mathematica notebook (.nb) file, filtering out binary graphics caches."
)
async def read_notebook_cells(notebook_path: str, max_cells: int = 100) -> str:
    """
    Args:
        notebook_path: Path to the .nb notebook file.
        max_cells: Maximum number of input cells to extract (default: 100).
    """
    nb_p = Path(notebook_path).expanduser().resolve()
    if not nb_p.exists():
        return f"File not found: {nb_p}"

    script = f"""
UsingFrontEnd[
    inputs = NotebookImport["{str(nb_p)}", "Input" -> "InputText"];
    Print["TOTAL_CELLS:", Length[inputs]];
    count = Min[{max_cells}, Length[inputs]];
    Do[
        Print["=== CELL ", i, " ==="];
        Print[inputs[[i]]];
    , {{i, 1, count}}];
];
Quit[];
"""
    stdout, stderr, _ = _execute_wolfram_code(script, 60)
    if "TOTAL_CELLS:" not in stdout and stderr.strip():
        return f"Error reading notebook: {stderr.strip()}"
    return stdout.strip()


@server.tool(
    name="wolfram_run_script",
    description="Execute an external Wolfram script (.wl or .wls file) and capture full console output."
)
async def wolfram_run_script(script_path: str, args: Optional[list[str]] = None, timeout_seconds: int = 300) -> str:
    """
    Args:
        script_path: Path to the .wl or .wls script to run.
        args: Optional list of command-line arguments to pass to the script.
        timeout_seconds: Maximum execution time in seconds (default: 300).
    """
    sc_p = Path(script_path).expanduser().resolve()
    if not sc_p.exists():
        return f"Script not found: {sc_p}"

    cmd = [WOLFRAM_KERNEL, "-noprompt", "-script", str(sc_p)]
    if args:
        cmd.extend(args)

    try:
        proc = subprocess.run(
            cmd,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=timeout_seconds,
            cwd=str(sc_p.parent)
        )
        stdout = proc.stdout.decode("utf-8", errors="replace")
        stderr = proc.stderr.decode("utf-8", errors="replace")
        res = []
        if stdout.strip():
            res.append(stdout.strip())
        if stderr.strip():
            res.append(f"Messages/Errors:\n{stderr.strip()}")
        return "\n\n".join(res) if res else "Script completed successfully with no output."
    except subprocess.TimeoutExpired:
        return f"Script timed out after {timeout_seconds} seconds."
    except Exception as e:
        return f"Execution failed: {str(e)}"


if __name__ == "__main__":
    # Run the standard Stdio MCP server
    asyncio.run(server.run_stdio_async())
