#!/bin/sh
do_start () {
    echo -n "Starting ${DAEMON_NAME}:"
    source $PYTHON_ROOT/bin/activate
    export LD_LIBRARY_PATH=$PYTHON_BASE/lib
    $PYTHON ${DAEMON_BIN} start ${DAEMON_OPTS}
    RETVAL=$?
}
do_stop () {
    echo -n "Stopping ${DAEMON_NAME}:"
    source $PYTHON_ROOT/bin/activate
    export LD_LIBRARY_PATH=$PYTHON_BASE/lib
    $PYTHON ${DAEMON_BIN} stop ${DAEMON_OPTS}
    RETVAL=$?
}
do_debug () {
    echo -n "Debugging: $PYTHON ${DAEMON_BIN} $@ ${DAEMON_OPTS}"
    source $PYTHON_ROOT/bin/activate
    export LD_LIBRARY_PATH=$PYTHON_BASE/lib
    $PYTHON ${DAEMON_BIN} $@ ${DAEMON_OPTS}
    RETVAL=$?
}

case "$1" in
    start|stop)
        do_${1}
        ;;

    debug)
        do_debug ${@:2}
        ;;

    restart|reload|force-reload)
        do_stop
        do_start
        ;;

    status)
        echo "Haven't implemented status"
        ;;

    *)
        echo "Usage: /etc/init.d/${DAEMON_NAME} {start|stop|restart|status}"
        exit 1
        ;;

esac
echo rc=$RETVAL
exit $RETVAL
