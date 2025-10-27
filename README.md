# Software Verification (2025)

## Office hours

Please inform before (by email) that you plan to attend office hours.

| Instructor    | Schedule | E-mail |
| ------------- | -------- | ------ |
| Mário Pereira | Monday, 14h00 (Office 243) | mjp.pereira@fct.unl.pt |

## Handouts

| Handout | Statement                           | Companion files                |
|---------|-------------------------------------|--------------------------------|
| 1       | [Handout 1 (.pdf)](sv_handout1.pdf) | [proper_cuts.v](proper_cuts.v) |
| 2       | [Handout 2 (.pdf)](sv_handout2.pdf) | [delannoy.zip](delannoy.zip)   |

## Installation procedures

Throughout the Software Verification course we will be using several
tools to illustrate different aspects of deductive verification. As
so, I will be updating this section with the main installation
procedures and guidelines for each tool and framework.

### The OCaml language and ecosystem

The OCaml language is the language of choice for the implementation
for some of the tools used in the Software Verification course. <!-- We are -->
<!-- going to use OCaml during lectures, to present fundamental concepts -->
<!-- about languages and compilers, as well as in practical sessions to -->
<!-- implement and experiment with some of the main concepts presented -->
<!-- during lectures. -->

In order to install OCaml and the language ecosystem, please follow
the installation guide provided [here](install_ocaml.md).

### The Rocq proof assistant

> [!WARNING]
> Until very recently, Rocq was called the "Coq Proof Assistant". It
> is very likely that installation procedures, tutorials, and every
> kind of available documentation refers to Rocq and Coq
> interchangeably.

The Rocq proof assistant is going to be our tool of choice for the
first part of the Software Verification course.

In order to install Rocq, you can find comprehensive instructions
[here](https://rocq-prover.org/install). There, you will found
instructions on how to install Coq under Linux, Windows, or MacOS.

The Rocq Platform is an easy way to install the Rocq Proof Assistant
and basic packages. It is available for Linux, Windows, and MacOS.

Regarding editors, Rocq comes with its own IDE. This is installed with
the Rocq Platform. There are also very smooth integration of the proof
assistant with common text editors, such as VS Code, Emacs, or Vim.

### The Why3 framework

The Why3 framework is going to be our tool of choice for the second
part of the Software Verification course.

In order to install Why3 and its ecosystem, please follow the
installation guide provided [here](install_why3.md).

The Why3 framework has been around for a few years now, and it has
been the subject of very intense development and research. You should
definitely know and check, on a regular basis, the following three
websites:

  - The framework manual: https://www.why3.org/doc/

    Other than providing a very comprehensive presentation of the
    framework and underlying tools, the third chapter is of mandatory
    reading for those learning to do proofs with Why3.

  - The standard library: https://www.why3.org/stdlib/

  - Finally, the huge gallery of verified programs:
    https://toccata.gitlabpages.inria.fr/toccata/gallery/why3.en.html

    This is probably the best source to learn specification and
    programming using WhyML, the programming language of Why3.

## Planning

| Week | Date | Topics | Slides | Labs |
| ---- | ---- | ------ | ------ | ---- |
| 1 | 9 Sep | Verified Functional Programs: introduction | [Lecture 1 (slides)](lecture1.pdf) <br> [Lecture Notes](notes_fp.pdf) | |
| 1 | 9, 10 Sep | Introduction to the Rocq Proof Assistant | | [Lab 1 (.pdf)](lab1/lab1.pdf) <br> [Rocq file (.v)](lab1/lab1.v) <br> [Solutions (.v)](lab1/lab1_solutions.v) |
| 2 | 16 Sep | Proof by induction | [Lecture 2 (slides)](lecture2.pdf) <br> [Lecture Notes](notes_induction.pdf) | |
| 2 | 16, 17 Sep | Exercises on proof by induction | | [Lab 2 (.pdf)](lab2/lab2.pdf) <br> [Rocq file (.v)](lab2/lab2.v) <br> [Solutions (.v)](lab2/lab2_solutions.v) |
| 3 | 23 Sep | Inductively defined properties and verification of abstract data types | [Lecture 3 (slides)](lecture3.pdf) <br> [Lecture Notes](notes_inductive_properties.pdf) | |
| 3 | 23, 24 Sep | Verified Skew Heaps | | [Lab 3 (.pdf)](lab3/lab3.pdf) <br> [Rocq file (.v)](lab3/lab3.v) <br> [Solutions (.v)](lab3/lab3_solutions.v) |
| 4 | 30 Sep | Introduction to Hoare Logic | [Lecture 4 (slides)](lecture4.pdf) <br> [Demo file (.mlw)](demo.mlw) <br> [Lecture Notes](notes_hoare_logic.pdf) <br> [First Handout Criteria](sv_handout1_evaluation_criteria.pdf) | |
| 4 | 31 Sep, 1 Oct | Support class for Handout 1 | | |
| 5 | 7 Oct | Loop Invariants in Hoare Logic and Weakest Precondition Calculus | [Lecture 5 (slides)](lecture5.pdf) <br> [Lecture Notes](notes_loops_wp.pdf) | |
| 5 | 7 Oct, 8 Oct | Introduction to the Why3 Tool | | [Lab 5 (.pdf)](lab5/lab5.pdf) <br> [Why3 file (.mlw)](lab5/lab5.mlw) <br> [Solutions (.zip)](lab5/lab5_solutions.zip) |
| 6 | 14 Oct | Loop Invariants, Sorting Algorithms, Bounded Integers | [Lecture 6 (slides)](lecture6.pdf) | |
| 6 | 14 Oct, 15 Oct | Exercises on Loop Invariants and Matrices |  | [Lab 6 (.pdf)](lab6/lab6.pdf) <br> [Solutions (.zip)](lab6/lab6_solutions.zip) |
| 7 | 21 Oct | Verification of Abstract Data Types and Ghost Code | [Lecture 7 (slides)](lecture7.pdf) | |
| 7 | 21 Oct, 22 Oct | More exercises on Matrices and Verification of an Abstract Data Type |   | [Lab 7 (.pdf)](lab7/lab7.pdf) <br> [Why3 file (.mlw)](lab7/lab7.mlw) <br> [Solutions (.zip)](lab7/lab7_solutions.zip)|
