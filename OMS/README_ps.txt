# 1. Apply patches to the Sage library:

     sage -sh
     cd $SAGE_ROOT/devel/sage
     hg qimport -P /path/to/changes_to_sagelib-5.10.patch

# 2. Copy files

#     The following should work fine (notice the trailing slash after OMS):
      sage -sh
      cp -r /path/to/OMS/ $SAGE_ROOT/devel/sage-main/

#  But if you're worried about overwriting things you can do the following instead:
      sage -sh
      cd $SAGE_ROOT/devel/sage-main/
      cp -r /path/to/OMS/.git .git
      cp /path/to/OMS/.gitignore .
      cp /path/to/OMS/README_ps.txt .
      cp /path/to/OMS/changes_to_sagelib-5.10.patch .
      cd sage/modular/
      cp -r /path/to/OMS/sage/modular/btquotients btquotients
      cp -r /path/to/OMS/sage/modular/pollack_stevens pollack_stevens
      cd overconvergent/
      cp -r /path/to/OMS/sage/modular/overconvergent/pollack pollack
      cp -r /path/to/OMS/sage/modular/overconvergent/families families

# 3. Rebuilding

Whenever you pull in changes from the repository or make your own
changes to these files, make sure to rebuild sage so that they take
effect:

     sage -b
