.. include:: /macros.rst

Continuous Integration
======================

Continuous integration (CI) is supported for XMHF-64, which catches compile
errors and simple runtime errors. Continuous integration can run in 3 platforms:

*
  GitHub Actions only compiles XMHF
*
  Jenkins compiles and runs XMHF, but it requires a self-hosted server
*
  Circle CI compiles and runs XMHF. The CI service is provided for free, but it
  is slower than Jenkins

The challenge with a lot of CI platforms is that running XMHF requires KVM.
However, a lot of platforms do not support this feature. So we support CI in
all 3 platforms above.

CI-related scripts are stored in ``xmhf-64/tools/ci``. Some CI platforms
require creating special folders in the root directory, covered in each section
below.

GitHub Actions
--------------

GitHub Actions is used to compile XMHF in a matrix of configurations, including

* 32-bit or 64-bit
* optimize (O3) or not optimize (O0)
* whether remove features that QEMU does not support (e.g. DRT, DMAP)

To enable GitHub actions, follow GitHub's documentation:
`https://docs.github.com/en/repositories/managing-your-repositorys-settings-and-features/enabling-features-for-your-repository/managing-github-actions-settings-for-a-repository <https://docs.github.com/en/repositories/managing-your-repositorys-settings-and-features/enabling-features-for-your-repository/managing-github-actions-settings-for-a-repository>`_

GitHub CI does not support virtualization features, so XMHF cannot run in
GitHub CI. As a result, we only compile XMHF in GitHub CI. The CI passes when
all configurations compile without error.

GitHub's configuration file is ``.github/workflows/build.yml``

Jenkins
-------

Jenkins runs in self-hosted server, so you need to configure a Linux machine
that supportes hardware virtualization and KVM in order to run Jenkins.

Jenkins's configuration file is ``xmhf-64/tools/ci/Jenkinsfile``

Installing Jenkins
^^^^^^^^^^^^^^^^^^

First install Java. On Debian this can be ``apt-get install openjdk-11-dbg``.
On Fedora this can be ``dnf install java-11-openjdk``.

Follow Jenkins's guide to install Jenkins:
`https://www.jenkins.io/doc/book/installing/linux/ <https://www.jenkins.io/doc/book/installing/linux/>`_

After installing, use a browser to navigate to
`http://127.0.0.1/8000/ <http://127.0.0.1/8000/>`_. Follow the web interface
to complete installation.

Installing prerequisits for XMHF
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The Jenkins pipeline does not contain logics to install packages.
Follow :doc:`Building </pc-intel-x86_64/build>`\ to install packages to build
XMHF (e.g. ``apt-get install build-essential crossbuild-essential-i386``).
Also install QEMU (TODO TODO TODO: doc).

Install extra packages needed by the pipeline:
Python 3, `gdown <https://pypi.org/project/gdown/>`_, and sshpass. For Fedora,
change ``apt-get`` below to ``dnf``.

.. code-block:: bash

   sudo apt-get install python3-pip sshpass
   python3 -m pip install gdown

The Jenkins user needs to run KVM. So add it to the ``kvm`` group

.. code-block:: bash

   sudo usermod -aG kvm jenkins

Creating a Pipeline for XMHF
^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Select "New Item". Give it a name (e.g. "xmhf-64") and the type is "Pipeline".
Then in "Pipeline", select "Definition" as "Pipeline script from SCM".

Under "General", check "Do not allow concurrent builds".

Under "Pipeline", enter the repository information in "SCM". Change "Script
Path" to ``xmhf-64/tools/ci/Jenkinsfile``.

Click "Save" to complete creating the pipeline. Click "Build Now" to start a
build. This build may fail, but it fetches pipeline parameters from the SCM.
After the first build the button should become "Build with Parameters". Click
on this button and then "Build" to start a build.

Circle CI
---------

To enable Circle CI, follow Circle CI's documentation:
`https://circleci.com/docs/2.0/create-project/ <https://circleci.com/docs/2.0/create-project/>`_

Circle CI supports KVM using nested virtualization, so we compile and run XMHF
here. The CI passes if XMHF compiles successfully and TrustVisor's PAL demo
passes.

Circle CI already runs in KVM, so XMHF runs in a nested KVM environment.
Consequently, XMHF is too slow to boot Linux. The configuration option
``--enable-optimize-nested-virt`` is added to Circle CI to make sure Linux can
boot successfully.

Circle CI's configuration file is ``.circleci/config.yml``


External dependencies
---------------------

QEMU images
^^^^^^^^^^^

Two QEMU images of Debian are downloaded from Google Drive to run the Jenkins
and Circle CI. See ``xmhf-64/tools/ci/download.sh`` for details.

* `debian11x86.qcow2 <https://drive.google.com/uc?id=1T1Yw8cBa2zo1fWSZIkry0aOuz2pZS6Tl>`_ is 2.9G
* `debian11x64.qcow2 <https://drive.google.com/uc?id=1WntdHCKNmuJ5I34xqriokMlSAC3KcqL->`_ is 3.3G

Once these images are downloaded, they are not downloaded again. In Jenkins,
these images are stored in the work directory. In Circle CI, these images are
cached.

GRUB
^^^^

GRUB modules are downloaded from Debian's packages mirror at `http://http.us.debian.org/debian/pool/main/g/grub2/grub-pc-bin_2.04-20_amd64.deb <http://http.us.debian.org/debian/pool/main/g/grub2/grub-pc-bin_2.04-20_amd64.deb>`_. (948K)

