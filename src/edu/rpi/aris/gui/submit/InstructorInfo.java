package edu.rpi.aris.gui.submit;

public class InstructorInfo implements AssignmentInfo {

    public InstructorInfo(int userId, int classId, int assignmentId, int proofId, int submissionId, String name, long timestamp, String status) {

    }

    @Override
    public int getNumColumns() {
        return 4;
    }

    @Override
    public Object getColumnData(int columnNum) {
        return null;
    }

    @Override
    public String getColumnName(int columnNum) {
        return null;
    }

    @Override
    public int compareTo(AssignmentInfo o) {
        return 0;
    }
}
