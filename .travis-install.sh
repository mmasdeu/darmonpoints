#! /bin/sh
set -e
cd $HOME
SAGE_IMAGE = `python2 process_mirror.py ${SAGE_SERVER} ${SAGE_AGE}`
if [ ! -x SageMath/sage ] ; then
    rm -f SageMath.tar.bz2
    wget ${SAGE_SERVER}${SAGE_IMAGE} -O SageMath.tar.bz2
    tar xf SageMath.tar.bz2
fi
MAKE="make -j4"
export MAKE
# Install packages
#SageMath/sage -i lrslib
# To initialize matplotlib font manager
SageMath/sage -python -c 'import matplotlib.pyplot'
