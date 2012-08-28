#!/bin/sh

USER=$1
if [ -z "$USER" ]
then
    USER=`whoami`
fi

rsync -vr doc $USER@web.sourceforge.net:/home/project-web/xmhf/htdocs
