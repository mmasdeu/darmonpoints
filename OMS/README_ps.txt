# 1. Make a clone of the git repository anywhere you want:

     cd /path/to/desired/location
     git clone git@github.com:roed314/OMS.git

# If this fails you can instead try

     git clone https://github.com/roed314/OMS.git

# 2. Apply patches to the Sage library:

     sage -sh
     cd $SAGE_ROOT/devel/sage
     hg qimport -P /path/to/changes_to_sagelib-5.10.patch

# 3. Copy files from your clone

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

## You should run git commands in $SAGE_ROOT/devel/sage-main.

# 4. Synchronize

     git pull
     git push

If changes_to_sagelib-5.10.patch changes, do this:

     sage -sh
     cd $SAGE_ROOT/devel/sage/
     hg qpop
     hg qrm   changes_to_sagelib-5.10.patch
     hg qimport -P /path/to/changes_to_sagelib-5.10.patch
     sage -br

Note that rebuilding after this may take quite a while (~30 minutes).

# 5. Rebuilding

Whenever you pull in changes from the repository or make your own
changes to these files, make sure to rebuild sage so that they take
effect:

     sage -b

# 5. Testing

# In some versions of sage if you use the symlink approach, when you
# test you must pass --force_lib.

     sage -t --force_lib

