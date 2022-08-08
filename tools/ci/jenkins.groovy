void build_xmhf(String subarch, String workdir, String build_opts) {
    PWD = sh(returnStdout: true, script: 'pwd').trim()
    sh "git clean -Xdf"
    // Workaround git 2.30 bug
    sh "rm -rf _build_lib* hypapps/trustvisor/src/objects/"
    sh "rm -rf hypapps/helloworld/app/objects/"
    sh "./tools/ci/build.sh ${subarch} ${build_opts}"
    sh "rm -rf ${workdir}"
    sh "mkdir ${workdir}"
    sh """
        python3 -u ./tools/ci/grub.py \
            --subarch ${subarch} \
            --xmhf-bin ${PWD}/ \
            --work-dir ${workdir} \
            --verbose \
            --boot-dir ${PWD}/tools/ci/boot
    """
}

return this
