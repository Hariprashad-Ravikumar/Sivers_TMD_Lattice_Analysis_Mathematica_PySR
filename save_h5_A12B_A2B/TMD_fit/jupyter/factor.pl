#!/usr/bin/perl

# $iters=$ARGV[0];
$iters=10;

$fine=1000;

$i=1;
while ( $i <= $fine ) {
   $j=1;
   while ( $j <= $fine ) {
      $f[$i][$j]=10000./(10000.+$i*$i+$j*$j);
      #      $f[$i][$j]=100./($i*$j);
      #      $f[$i][$j]=100.*exp(-1.*$i*$j);
      #      $f[$i][$j]=100.*exp(-0.0001*($i*$i+$j*$j));
      $j++;
   };
   $i++;
};

$i=1;
while ( $i <= $fine ) {
   $g[$i]=1;
   $i++;
};


$k=1;
while ( $k <= $iters ) {


$g2sum=0;
$i=1;
while ( $i <= $fine ) {
   $g2sum=$g2sum+$g[$i]*$g[$i];
   $i++;
};
$g2sum=$g2sum/$fine;

$j=1;
while ( $j <= $fine ) {
   $fgsum[$j]=0;

   $i=1;
   while ( $i <= $fine ) {
      $fgsum[$j]=$fgsum[$j]+$f[$i][$j]*$g[$i];
      $i++;
   };
   $fgsum[$j]=$fgsum[$j]/$fine;
   $fgsum[$j]=$fgsum[$j]/$g2sum;

   $j++;
};

$fgsum2sum=0;
$j=1;
while ( $j <= $fine ) {
   $fgsum2sum=$fgsum2sum+$fgsum[$j]*$fgsum[$j];
   $j++;
};
$fgsum2sum=$fgsum2sum/$fine;

$i=1;
while ( $i <= $fine ) {
   $ffsum[$i]=0;

   $j=1;
   while ( $j <= $fine ) {
      $ffsum[$i]=$ffsum[$i]+$f[$i][$j]*$fgsum[$j];
      $j++;
   };
   $ffsum[$i]=$ffsum[$i]/$fine;
   $ffsum[$i]=$ffsum[$i]/$fgsum2sum;

   $i++;
};

$i=1;
while ( $i <= $fine ) {
   $g[$i]=$ffsum[$i];
   $i++;
};

$j=1;
while ( $j <= $fine ) {
   $h[$j]=$fgsum[$j];
   $j++;
};


   $k++;
};


$orignorm=0;
$ms=0;
$i=1;
while ( $i <= $fine ) {
   $j=1;
   while ( $j <= $fine ) {
      $diff=$f[$i][$j]-$g[$i]*$h[$j];
      $orignorm=$orignorm+$f[$i][$j]*$f[$i][$j];
      $ms=$ms+$diff*$diff;
      #      print "$i $j $diff\n";
      #      print "$i $j $f[$i][$j]\n";
      $j++;
   };
   $i++;
};
$ms=$ms/($fine*$fine);
$orignorm=$orignorm/($fine*$fine);
$ratio=$ms/$orignorm;
$rratio=sqrt($ratio);

print "relative root mean square distance to original function: $rratio\n";


exit(0);

