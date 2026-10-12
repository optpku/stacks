/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.Nakayama.Basic
public import ReasLib.RingTheory.Ideal.Nakayama.Localization

@[expose] public section

/-!
# Nakayama criteria

@stack 00DV
@stack 0GLX

This is the stable shared entry point.  Basic quotient/Jacobson/nilpotent
criteria and finite localization criteria are maintained in separate leaves;
downstream consumers may import this module without knowing that split.
-/
