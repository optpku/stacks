/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ZariskiCover.Basic
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u v

/- Definition 65.12.5: let `S` be a scheme and let `F` be an algebraic space over `S`.
A Zariski covering `{Fᵢ ⊂ F}_{i ∈ I}` of `F` is given by a set `I` and a collection of
open subspaces `Fᵢ ⊂ F` such that `∐ Fᵢ ⟶ F` is a surjective map of sheaves. -/

@[stacks 02YY] #check (AlgebraicGeometry.AlgebraicSpace.ZariskiCover.{u, v} :
  {S : Scheme.{u}} → AlgebraicGeometry.AlgebraicSpace S → Type (max (u + 1) (v + 1)))
