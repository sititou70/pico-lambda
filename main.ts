#!/usr/bin/env -S npm exec -- ts-node

import fs from "fs";
import { parse } from "./parser/parser";
import { evaluate } from "./evaluator/evaluator";
import { print, printType } from "./printer/printer";
import { program } from "commander";
import { inferType } from "./checker/checker";

const main = () => {
  program.option("-s, --skip-tc", "Skip type checking");
  program.parse();
  const options = program.opts();
  const skip_tc = options.skipTc;

  const input_path = process.argv[2];
  const input = fs.readFileSync(input_path).toString();

  const parse_result = parse(input);
  if (!parse_result.success) {
    console.error("parsing failed");
    console.dir(parse_result.error, { depth: null });
    return;
  }

  if (!skip_tc) {
    const infer_result = inferType(parse_result.value);
    if (!infer_result.success) {
      console.error("type checking failed");
      console.dir(infer_result.error, { depth: null });
      return;
    }

    console.log("tc passed:", printType(infer_result.value));
  }

  const evaluate_result = evaluate(parse_result.value);
  if (!evaluate_result.success) {
    console.error("evaluating failed");
    console.dir(evaluate_result.error, { depth: null });
    return;
  }

  const print_result = print(evaluate_result.value);
  console.log(print_result);
};
main();
