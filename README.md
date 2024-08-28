# EffiTaint

EffiTaint is a novel static taint analysis tool designed to address the limitations of existing tools such as FlowDroid and Tai-e. It offers enhanced accuracy and performance in tracking sensitive data flows in Java programs, particularly in large-scale applications. EffiTaint introduces several innovations, including efficient source chain optimization and accurate array modeling, making it a robust solution for modern software security needs.

## Features

- **On-Demand Pointer Flow Graph (PFG) Construction**: Constructs PFGs without relying on a complete call graph, improving analysis speed and efficiency.
- **Flow-Sensitive Taint Analysis**: Enhances the precision of taint tracking by refining taint propagation models, particularly for array operations and control flows.
- **Selective Taint Analysis**: Reduces analysis overhead by focusing on relevant methods and paths, significantly improving performance.
- **Improved Source and Sink Matching**: Uses a coarse-grained matching strategy to uncover more potential taint flows, improving the recall rate in taint analysis.
- **Array Modeling**: Provides fine-grained handling of one-dimensional and two-dimensional arrays to minimize false positives in taint tracking.

## Key Modifications from Tai-e

EffiTaint introduces significant modifications to the original Tai-e project, including:

- **EffitaintSolver**: Rewritten the `defaultSolver` from Tai-e as `EffitaintSolver` and modified related plugins to ensure compatibility.
- **Taint Analysis Modules**: Rewritten the `SourceHandler` and `TransferHandler` modules, and introduced a new `TaintAnalysisHandler` module for enhanced taint tracking.
- **Reflection Analysis**: Added reflection analysis specifically for the `Field.get()` method in the reflection plugin, improving the handling of reflective access patterns.
- **...**


## Installation

To install and set up EffiTaint:

1. Clone the repository:
   ```bash
   git clone https://github.com/tehdlee/Effitaint.git
2. Navigate to the project directory:
   ```bash
   cd Effitaint
3. Build the project using your preferred build tool (Gradle).EffiTaint has been implemented in IntelliJ IDEA. The usage in IntelliJ IDEA is consistent with Tai-e. For detailed instructions on how to use EffiTaint in IntelliJ IDEA, please refer to the [Tai-e setup guide](https://tai-e.pascal-lab.net/docs/current/reference/en/setup-in-intellij-idea.html).
## Usage
EffiTaint can be integrated into your Java projects to analyze taint flows. Follow these steps to use EffiTaint:

1. Configure the sources and sinks in the configuration files.We recommend using the configuration file (.yml) suggested by Tai-e to configure sources, sinks, and a series of other settings. You can refer to the examples provided in the `config/common` directory for more details.
2. Run the analysis with the provided scripts.Set the command line parameter as follows:

    ```bash
    --options-file=config/common/XXX.yml

3. View the analysis reports generated in the output directory.

### Integration and Usage of Jasmine Analysis

1. Jasmine module is included by default. If not needed, you can remove it in the configuration file.
2. To integrate Jasmine framework, simply add the following code:

   **Import the following package:**

    ```java
    import jasmine.analysis.CreateEdge;
    ```

   **Then, insert the following code in the `build()` of `SootWordBuilder.java`:**

    ```java
    CreateEdge edge = new CreateEdge();
    String path = System.getProperty("user.dir") + File.separator + "src/main/resources/config.properties";
    edge.initCallGraph(path);
    ```

## Benchmarks
EffiTaint has been tested on the SecuriBench Micro suite, showing superior performance compared to FlowDroid and Tai-e:

- **Accuracy:** 97.0%
- **Recall:** 98.3%
- **Average Runtime:** 26.93 seconds
- **Memory Consumption:** 0.67 GB
## Contributing
We welcome contributions to EffiTaint! If you have ideas for new features, optimizations, or bug fixes, please feel free to open an issue or submit a pull request.

## Acknowledgments

EffiTaint is built upon the foundations provided by the Tai-e project. For more information about the original Tai-e project, please visit [Tai-e GitHub Repository](https://github.com/pascal-lab/Tai-e.git).

EffiTaint also integrates with the Jasmine project to enhance its static taint analysis capabilities for Spring framework projects. For more details, visit the [Jasmine GitHub Repository](https://github.com/SpringJasmine/Jasmine.git).


## License
EffiTaint is licensed under the LGPL v3.0 and GPL v3.0 licenses. For more details, see the LICENSE file.
