#!/usr/bin/perl

@files = <../flat/quad-*>;



foreach $file (@files) {
    print "\n" .$file . "\n";

    system("./z3str_run.sh " . $file );

}

