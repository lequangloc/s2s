#!/usr/bin/perl

@files = <*/*.smt2>;

foreach $file (@files) {
    print $file . "\n";

    system("../../../src/smt2sl/smt2sl " . $file);
}







