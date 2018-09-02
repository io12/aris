package edu.rpi.aris.assign.message;

import edu.rpi.aris.assign.*;
import edu.rpi.aris.assign.spi.ArisModule;

import java.io.PipedInputStream;
import java.io.PipedOutputStream;
import java.sql.Connection;
import java.sql.PreparedStatement;

public class ProblemEditMsg<T extends ArisModule> extends ProblemMessage<T> {

    private final int pid;
    private final String name;

    public ProblemEditMsg(int pid, String name) {
        this(pid, name, null, null);
    }

    public ProblemEditMsg(int pid, String moduleName, Problem<T> problem) {
        this(pid, null, moduleName, problem);
    }

    public ProblemEditMsg(int pid, String name, String moduleName, Problem<T> problem) {
        super(moduleName, problem);
        this.pid = pid;
        this.name = name;
    }

    // DO NOT REMOVE!! Default constructor is required for gson deserialization
    private ProblemEditMsg() {
        super(null, null);
        pid = 0;
        name = null;
    }

    @Override
    public ErrorType processMessage(Connection connection, User user) throws Exception {
        if (!UserType.hasPermission(user, UserType.INSTRUCTOR))
            return ErrorType.UNAUTHORIZED;
        if (name != null) {
            try (PreparedStatement updateName = connection.prepareStatement("UPDATE problem SET name = ? WHERE id = ?")) {
                updateName.setString(1, name);
                updateName.setInt(2, pid);
                updateName.executeUpdate();
            }
        }
        if (getProblem() != null) {
            ArisModule<T> module = ModuleService.getService().getModule(getModuleName());
            ProblemConverter<T> converter = module.getProblemConverter();
            try (PreparedStatement updateData = connection.prepareStatement("UPDATE problem SET data = ? WHERE id = ?");
                 PipedInputStream pis = new PipedInputStream();
                 PipedOutputStream pos = new PipedOutputStream(pis)) {

                converter.convertProblem(getProblem(), pos, false);
                pos.close();
                updateData.setBinaryStream(1, pis);

                updateData.setInt(2, pid);
                updateData.executeUpdate();
            }
        }
        return null;
    }

    @Override
    public MessageType getMessageType() {
        return MessageType.EDIT_PROBLEM;
    }

    @Override
    public boolean checkValid() {
        return pid > 0 && super.checkValid();
    }

    public int getPid() {
        return pid;
    }

}