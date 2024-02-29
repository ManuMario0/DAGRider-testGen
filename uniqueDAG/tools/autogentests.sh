#! /bin/bash
#
# Generate tests automatically from TLA+ spec and a configuration file
#

echo "Starting ..."

startTime=$((`date +%s`))
workingDir="Tests_"`date +%Y-%m-%dT%H-%M-%S`

mkdir $workingDir

while read p; do
	subdirname=`echo "$p" | sed 's/Name?\([a-zA-Z][a-zA-Z0-9]*\);[^;]*;[^;]*;[^;]*;[^;]*;[^;]*;[^;]*/\1/'`
	subdir=$workingDir/$subdirname
	mkdir $subdir

	currentTime=`date +%H:%M:%S`
	echo "[ $currentTime ] Processing $subdirname"

	iterations=$((`echo "$p" | sed 's/[^;]*;Count?\([0-9][0-9]*\);[^;]*;[^;]*;[^;]*;[^;]*;[^;]*/\1/'`))

	numProcess=`echo "$p" | sed 's/[^;]*;[^;]*;NumProcess?\([0-9]*\);[^;]*;[^;]*;[^;]*;[^;]*/\1/'`
	numWaves=`echo "$p" | sed 's/[^;]*;[^;]*;[^;]*;NumWaves?\([0-9]*\);[^;]*;[^;]*;[^;]*/\1/'`
	tlaFileContent=`sed "s/pp/$numProcess/;s/ww/$numWaves/" < templates/template.tla`

	depth=`echo "$p" | sed 's/[^;]*;[^;]*;[^;]*;[^;]*;Depth?\([0-9]*\);[^;]*;[^;]*/\1/'`

	tlaFileName=MC.tla
	echo $tlaFileContent > $subdir/$tlaFileName
	
	inv=`echo "$p" | sed 's/[^;]*;[^;]*;[^;]*;[^;]*;[^;]*;Inv?\([^;]*\);[^;]*/\1/'`
	inv=`echo "$inv" | sed 's/\\\\/\\\\\\\\/g'`

	constraints=`echo "$p" | sed 's/[^;]*;[^;]*;[^;]*;[^;]*;[^;]*;[^;]*;Constraints?\([^;]*\)/\1/'`
	constraints=`echo "$constraints" | sed 's/\\\\/\\\\\\\\/g'`

	setInvConst=`sed "s/%%Inv%%/${inv}/;s/%%Constraints%%/${constraints}/" < templates/UniqueDAGSpec.tla`

	echo "$setInvConst" > $subdir/UniqueDAGSpec.tla

	for (( i=0; i < $iterations; i++ )); do
			outputFile=test$i.out
			
			java -XX:+UseParallelGC \
					-jar "$TLAEclipseDir/tla2tools.jar" \
					-seed $i -simulate -depth $depth -deadlock \
					-config templates/MC.cfg \
					$subdir/$tlaFileName > $subdir/$outputFile
			rm -r states/*
	done
done < $1

rm -r states

endTime=`date +%s`
execTimeMin=$(( (endTime- startTime) / 60))
execTimeSec=$(( (endTime- startTime) % 60))
echo "Finished generating tests in $execTimeMin min and $execTimeSec sec"
