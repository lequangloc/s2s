#!/usr/bin/perl

@files = <slcomp/qf_shlid_entl/*.ss>;

foreach $file (@files) {
    print "\n" . $file . "\n";

    system("timeout 600 ./ksolver " . $file);
}

