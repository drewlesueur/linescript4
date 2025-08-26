<?php
$loopCount = 1000000;
$val = 0;
$startTime = microtime(true);
for ($i = 0; $i < $loopCount; $i++) {
    $val = $i - 0.1 + $val;
}
$endTime = microtime(true);
$executionTime = ($endTime - $startTime) * 1000;
echo "Execution time: " . $executionTime . " milliseconds\n";
echo "val is " . $val . "\n";


echo "---\n";

$code = '
$loopCount = 1000000;
$val = 0;
$startTime = microtime(true);
for ($i = 0; $i < $loopCount; $i++) {
    $val = $i - 0.1 + $val;
}
$endTime = microtime(true);
$executionTime = ($endTime - $startTime) * 1000;
echo "Execution time: " . $executionTime . " milliseconds\n";
echo "val is " . $val . "\n";
';

eval($code);

echo "---\n";

$loopCount = 1000000;
$val = 0;
$startTime = microtime(true);
for ($i = 0; $i < $loopCount; $i++) {
    eval('$val = $i - 0.1 + $val;');
}
$endTime = microtime(true);
$executionTime = ($endTime - $startTime) * 1000;
echo "Execution time: " . $executionTime . " milliseconds\n";
echo "val is " . $val . "\n";


echo "---\n";


convert this to perl
maintain the concept of eval, it's for testing

```perl
use Time::HiRes qw(gettimeofday tv_interval);

my $loopCount = 1000000;
my $val = 0;
my $startTime = [gettimeofday];
for (my $i = 0; $i < $loopCount; $i++) {
    $val = $i - 0.1 + $val;
}
my $endTime = [gettimeofday];
my $executionTime = tv_interval($startTime, $endTime) * 1000;
print "Execution time: $executionTime milliseconds\n";
print "val is $val\n";

print "---\n";

my $code = '
my $loopCount = 1000000;
my $val = 0;
my $startTime = [gettimeofday];
for (my $i = 0; $i < $loopCount; $i++) {
    $val = $i - 0.1 + $val;
}
my $endTime = [gettimeofday];
my $executionTime = tv_interval($startTime, $endTime) * 1000;
print "Execution time: $executionTime milliseconds\n";
print "val is $val\n";
';

eval $code;

print "---\n";

$loopCount = 1000000;
$val = 0;
$startTime = [gettimeofday];
for (my $i = 0; $i < $loopCount; $i++) {
    eval('$val = $i - 0.1 + $val;');
}
$endTime = [gettimeofday];
$executionTime = tv_interval($startTime, $endTime) * 1000;
print "Execution time: $executionTime milliseconds\n";
print "val is $val\n";

print "---\n";
```