/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Standard.Covering

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.Scheme

/- Definition 59.20.1: for `τ` equal to fppf, syntomic, smooth, étale, or
Zariski, a family of morphisms of schemes with fixed target is a `τ`-covering
when its members have the corresponding morphism property and their images
jointly cover the target. The fppf branch follows this passage's literal
finite-presentation condition, rather than the locally finite-presentation
condition in the referenced fppf definition and canonical precoverage. -/
@[stacks 03X8] #check (AlgebraicGeometry.Scheme.StandardCovering :
  {T : Scheme.{u}} → (τ : StandardTopology) → {ι : Type v} →
    (X : ι → Scheme.{u}) → (f : ∀ i, X i ⟶ T) → Prop)

/- The pointwise characterization of a standard `τ`-covering family. -/
#check (AlgebraicGeometry.Scheme.standardCovering_iff :
  ∀ {T : Scheme.{u}} (τ : StandardTopology) {ι : Type v}
    (X : ι → Scheme.{u}) (f : ∀ i, X i ⟶ T),
    StandardCovering τ X f ↔
      (∀ x : T, ∃ i, x ∈ Set.range (f i)) ∧
        ∀ i,
          match τ with
          | .zariski => IsOpenImmersion (f i)
          | .etale => Etale (f i)
          | .smooth => Smooth (f i)
          | .syntomic => Syntomic (f i)
          | .fppf => Flat (f i) ∧ Scheme.Hom.FinitePresentation (f i))

end AlgebraicGeometry.Scheme
