package pascal.taie.analysis;


import soot.G;
import soot.Scene;
import soot.SootClass;
import soot.options.Options;

public class checkIR {
    public static void main(String[] args) {
        // 确保 Soot 的全局状态被初始化
        G.reset();

        // 设置 Soot 选项
        Options.v().set_prepend_classpath(true);
        Options.v().set_process_dir(java.util.Collections.singletonList("/home/haocheng/Z_personal/Research/projects/Tai-e2/Tai-e/java-benchmarks/java-sec-code-new/java-sec-code/target/classes")); // 指定要分析的类文件目录
        Options.v().set_whole_program(true);
        Options.v().set_allow_phantom_refs(true);

        // 加载并处理类
        Scene.v().loadNecessaryClasses();

        // 获取要分析的类
        SootClass sootClass = Scene.v().getSootClass("org.joychou.controller.SQLI"); // 替换为你要分析的类

        // 打印类的中间表示
        System.out.println(sootClass.getName() + " in Jimple format:");
        sootClass.getMethods().forEach(method -> {
            System.out.println(method.getSignature());
            System.out.println(method.retrieveActiveBody().toString());
        });
    }
}

