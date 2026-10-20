/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FunctionField.Unramified
public import ReasLib.AlgebraicGeometry.Scheme.FunctionField.Inertia
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.FunctionFieldExtension

/- The henselian conditions below quantify over chosen henselizations.  This is the
   representation-independent form of the source's conditions, since such choices are only
   determined up to a local algebra isomorphism. -/

/- Lemma 58.13.4 (1): for the normalization `ν` of an integral normal scheme `X` in a finite
extension `L` of its function field, the following are equivalent: unramifiedness of `X` in `L`
in the sense of Stacks 0BQJ, which is `Unramified ν`; `Unramified ν`; `Etale ν`; finite étaleness
`IsFinite ν ∧ Etale ν`; unramifiedness of the pullback of `ν` to `Spec O_{X,x}`; the same after
base change to any henselization of `O_{X,x}`; the same after base change to any strict
henselization of `O_{X,x}`; and étale scheme-theoretic fibres of degree at least `[L : K]`. -/
@[stacks 0BTF]
#check (AlgebraicGeometry.Scheme.FunctionFieldExtension.unramified_tfae_local_criteria :
    ∀ (X : Scheme.{u}) [IsIntegral X] (hX : X.isNormal)
    (L : Type u) [Field L] [Algebra X.functionField L]
    [FiniteDimensional X.functionField L],
    let ν := (map X L).fromNormalization
    List.TFAE
      [ Unramified ν
      , Etale ν
      , IsFinite ν ∧ Etale ν
      , ∀ x : X, Unramified (pullback.snd ν (X.fromSpecStalk x))
      , ∀ (x : X) (Rh : Type u) [CommRing Rh]
          [Algebra (X.presheaf.stalk x) Rh]
          [IsHenselizationOf (X.presheaf.stalk x) Rh],
          let g : Spec (CommRingCat.of Rh) ⟶ X :=
            Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) Rh)) ≫
              X.fromSpecStalk x
          Unramified (pullback.snd ν g)
      , ∀ (x : X) (Rsh : Type u) [CommRing Rsh]
          [Algebra (X.presheaf.stalk x) Rsh]
          [IsStrictHenselizationOf (X.presheaf.stalk x) Rsh],
          let g : Spec (CommRingCat.of Rsh) ⟶ X :=
            Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) Rsh)) ≫
              X.fromSpecStalk x
          Unramified (pullback.snd ν g)
      , ∀ x : X,
          Etale (ν.fiberToSpecResidueField x) ∧
            Module.finrank X.functionField L ≤ ν.fiberDegree x
      ])

/- Lemma 58.13.4 (2): if `L / K` is Galois, the previous criteria are also equivalent to
trivial inertia `I_y = ⊥` at every point of the normalization. -/
@[stacks 0BTF]
#check (AlgebraicGeometry.Scheme.FunctionFieldExtension.unramified_iff_trivial_inertia :
    ∀ (X : Scheme.{u}) [IsIntegral X] (hX : X.isNormal)
    (L : Type u) [Field L] [Algebra X.functionField L]
    [FiniteDimensional X.functionField L] [IsGalois X.functionField L],
    let ν := (map X L).fromNormalization
    Unramified ν ↔ ∀ y : (map X L).normalization, inertia X L y = ⊥)

end AlgebraicGeometry.Scheme.FunctionFieldExtension
