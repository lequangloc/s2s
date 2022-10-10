#!/usr/bin/perl

@files = <../flat/quad-*>;



foreach $file (@files) {
    print "\n" .$file . "\n";

    system("./tosmt2_run.sh " . $file . " > " . $file . ".smt2");

}

