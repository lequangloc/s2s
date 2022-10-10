#!/usr/bin/perl

@files = <../flat/quad-*>;



foreach $file (@files) {
    print "\n" .$file . "\n";

    system("./s3_run.sh " . $file );

}

