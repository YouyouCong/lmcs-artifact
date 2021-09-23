# A Functional Abstraction of Typed Invocation Contexts (Artifact)

This artifact includes an Agda formalization of our typed calculus of
`control`/`prompt` and CPS translation.
The code is checked using Agda version 2.6.0.1.

- `lambdaf.agda`: The λF calculus presented in Sections 3 and 5.
The function `go` serves as the proof of termination (Theorem 5).
The expression `exp4` represents example (2) from Section 2.
The expression `shift` represents the encoding of the `shift` operator
(Theorem 6).

- `lambdaf-red.agda`: The reduction rules of λF.
The relation `Reduce` serves as the proof of preservation (Theorem 1).

- `cps.agda`: The λC calculus and CPS translation presented in Sections 
4 and 6.
The `cpse` function serves as the proof of type preservation (Theorem 4).

- `lambdac-red.agda`: The reduction rules of λC.
The relation `Reduce` serves as the proof of the preservation property.

- `lambdaf-fg.agda`: The fine-grained λF calculus presented in Section 7.
The function `go` serves as the proof of termination (Theorem 9).
The expression `shift` represents the encoding of the `shift` operator
(Theorem 10).

- `lambdaf-fg-red.agda`: The reduction rules of the fine-grained λF.
The relation `Reduce` serves as the proof of preservation (part of 
Theorem 7).

- `cps-selective.agda`: The λC calculus and selective CPS translation 
presented in Sections 4, 6, and 7.
The `cpse` function serves as the proof of type preservation (Theorem 8).
