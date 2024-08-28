package pascal.taie.analysis;


import java.io.BufferedReader;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

public class transfer {
    public static void main(String[] args) {
        String baseAddress = "/home/haocheng/Z_personal/Research/projects/Jasmine_flowdroid_2/FlowDroid_Jasmine/soot-infoflow-android/";
        String outBaseAddress = "/home/haocheng/Z_personal/Research/projects/Tai-e2/Tai-e/config/output/taintyml/";
        String inputFilePath = baseAddress+"SourcesAndSinks-favorites-web.txt";
        String outputFilePath = outBaseAddress+"favorites-web-taint-config.yml";

        try (BufferedReader reader = new BufferedReader(new FileReader(inputFilePath));
             FileWriter writer = new FileWriter(outputFilePath)) {

            List<String> sources = new ArrayList<>();
            List<String> sinks = new ArrayList<>();
            String line;

            while ((line = reader.readLine()) != null) {
                if (line.contains("-> _SOURCE_")) {
                    String method = line.split("->")[0].trim();
                    int paramCount = getParameterCount(method);

                    for (int i = 0; i < paramCount; i++) {
                        sources.add(String.format("  - { kind: param, method: \"%s\", index: %d }", method, i));
                    }
                } else if (line.contains("-> _SINK_")) {
                    String method = line.split("->")[0].trim();
                    int paramCount = getParameterCount(method);

                    for (int i = 0; i < paramCount; i++) {
                        sinks.add(String.format("  - { vuln: \"any\", level: 4, method: \"%s\", index: %d }", method, i));
                    }
                }
            }

            writer.write("sources:\n");
            for (String source : sources) {
                writer.write(source + "\n");
            }

            writer.write("sinks:\n");
            for (String sink : sinks) {
                writer.write(sink + "\n");
            }

        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    private static int getParameterCount(String method) {
        // 获取方法参数列表的起始和结束位置
        int start = method.indexOf('(');
        int end = method.indexOf(')');

        if (start < 0 || end < 0 || start > end) {
            return 0;
        }

        String params = method.substring(start + 1, end).trim();
        if (params.isEmpty()) {
            return 0;
        }

        return params.split(",").length;
    }
}

