#!/usr/bin/perl

@files = <slcomp/qf_shls_entl/*.ss>;

foreach $file (@files) {
    print "\n" . $file . "\n";

    system("timeout 600 ./ksolver " . $file);
}

