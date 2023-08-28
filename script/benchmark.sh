#!/bin/bash
# Example SLURM job script for serial (non-parallel) jobs
#
# SLURM defaults to the directory you were working in when you submitted the job.
# Output files are also put in this directory. To set a different working directory add:
#
##SBATCH –-workdir=/mnt/nfs/home/c3054737/dlinear4
#
# Tell SLURM if you want to be emailed when your job starts, ends, etc.
#
##SBATCH --mail-type=ALL
#
# set up a job array with tasks numbered 1 to 100.
#SBATCH --array=0-3
#
# request one core per task
#SBATCH -c 1
#
# give the array a single job name
#SBATCH -J dlinear-benchmark
#
# Use custom files for both stdout and stderr
#
#SBATCH -o job/job_%A_%a.out
#SBATCH -e job/job_%A_%a.err
#
shopt -s nullglob

# Create an array with all the files in the smt2 direcory.
# They are also sorted to ensure reproducibility
input_files=(smt2/*)
IFS=$'\n' input_files=($(sort <<<"${input_files[*]}"))
unset IFS

file="${input_files[$SLURM_ARRAY_TASK_ID]}"
filename=$(basename "$file")
filename="${filename%.*}"

./benchmark -f "smt2/$filename.smt2" -o "csv/$filename.csv" --config benchmark.conf

