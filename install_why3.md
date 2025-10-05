# Why3 Installation

> [!WARNING]
> You should only proceed with installing the Why3 framework if you
> have already completed the installation procedures for
> OCaml. Instructions can be found [here](install_ocaml.html).

## The Why3 Framework

Having fully-functional OCaml system, installing `why3`, together with
its IDE, is as easy as doing

```console
opam install why3 why3-ide
```

After a few moments, the installation should succeed. Then, you can
test it by typing

```console
why3 --version
```

where you should get something like
`Why3 platform, version 1.XXX.YYY`.

## Installing External Provers

### Via Opam

We will be mainly using the `Why3` framework for deductive
verification of programs. In order to do so, we will be needing some
external provers (namely SMT solvers) to be able to discharge
generated verification conditions.

We shall start by installing SMT solvers that are available via
`opam`. Do the following:

```console
opam install alt-ergo z3
```

This will install the `Alt-Ergo` and `Z3` solvers on your machine. It
may take a few minutes to complete. After this, you can test your
installation by doing both `alt-ergo --version` and `z3 --version`.

### Other Solvers

There are many provers available, off-the-shelf. Even if `Alt-Ergo`
and `Z3` might suffice for use case scenarios, you want to take fully
advantage of the `Why3` ability to interface with many different
solvers. So, let me show you how to install a few more.

#### CVC5

I recommend you to install a pre-built binary of CVC5. You can find
the latest releases here: https://github.com/cvc5/cvc5/releases/

What I do for Linux: I take the `cvc5` binary and copy it to a `\bin`
folder that is in my `$PATH` variable. You might need to make the
binary executable after doing this. In Linux, this is done by

```console
chmod +x cvc5
```

Me personally, I am using `CVC5-1.1.0` since this one of the easiest
to pick the Linux binary from the *Releases assets*.

#### Eprover

The `Eprover` solver might come at handy when dealing with existential
quantification. Otherwise, it is also a very efficient prover when it
comes to reason about linear arithmetic.

You should find installation instructions, both for MacOS and Linux,
[here](https://wwwlehre.dhbw-stuttgart.de/~sschulz/E/Download.html)

## Making Why3 to Recognize Installed Solvers

After installing a new solver, you should type

```console
why3 config detect
```

Do not bother about the output. Just make sure `Why3` was able to find
all the provers we installed. Now, every time you open the `Why3 IDE`,
you should be able to use as many different solvers on your proofs, as
those that were recognized by `Why3`.
