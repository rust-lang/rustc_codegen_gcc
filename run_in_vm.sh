#!/bin/bash

vm_parent_dir=${CG_GCC_VM_DIR:-$(pwd)}
vm_dir=vm
exe=$1
exe_filename=$(basename $exe)
vm_home_dir=$vm_parent_dir/$vm_dir/home
vm_exe_path=$vm_home_dir/$exe_filename
inside_vm_exe_path=/home/$exe_filename
sudo cp $exe $vm_exe_path

shift
pushd $vm_parent_dir
sudo chroot $vm_dir qemu-m68k-static $inside_vm_exe_path $@
popd
