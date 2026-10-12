/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.GlobalSections
public import ReasLib.AlgebraicGeometry.WeilCohomology.PreWeil.AxiomA8

@[expose] public section

noncomputable section

open CategoryTheory
open AlgebraicGeometry

universe u v w

#check (AlgebraicGeometry.SchemeOverField.globalSectionsSpec :
  ∀ {k : Type u} [Field k], SchemeOverField k → SchemeOverField k)

#check (AlgebraicGeometry.SchemeOverField.toSpecΓ_over :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k),
    X.left.toSpecΓ ≫
      (AlgebraicGeometry.SchemeOverField.globalSectionsSpec X).hom = X.hom)

#check (AlgebraicGeometry.SchemeOverField.toGlobalSectionsSpec :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k),
    X ⟶ AlgebraicGeometry.SchemeOverField.globalSectionsSpec X)

#check (AlgebraicGeometry.SchemeOverField.toGlobalSectionsSpec_left :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k),
    (AlgebraicGeometry.SchemeOverField.toGlobalSectionsSpec X).left = X.left.toSpecΓ)

#check (WeilCohomology.PreWeilTheory.SatisfiesAxiomA8 :
  ∀ {k : Type u} [Field k]
    {F : Type v} [Field F] [CharZero F]
    {TateLine : Type w} [AddCommGroup TateLine] [Module F TateLine]
    {H Picard Cycle : ULiftHom.{u + 1} (SchemeOverField k) → Type w}
    [∀ X, Ring (H X)] [∀ X, Algebra F (H X)]
    [∀ X, AddCommGroup (Picard X)] [∀ X, Ring (Cycle X)],
    WeilCohomology.PreWeilTheory F TateLine
      (ULiftHom.{u + 1} (SchemeOverField k)) H Picard Cycle → Prop)

#check (WeilCohomology.PreWeilTheory.satisfiesAxiomA8_iff :
  ∀ {k : Type u} [Field k]
    {F : Type v} [Field F] [CharZero F]
    {TateLine : Type w} [AddCommGroup TateLine] [Module F TateLine]
    {H Picard Cycle : ULiftHom.{u + 1} (SchemeOverField k) → Type w}
    [∀ X, Ring (H X)] [∀ X, Algebra F (H X)]
    [∀ X, AddCommGroup (Picard X)] [∀ X, Ring (Cycle X)]
    (T : WeilCohomology.PreWeilTheory F TateLine
      (ULiftHom.{u + 1} (SchemeOverField k)) H Picard Cycle),
    T.SatisfiesAxiomA8 ↔
      ∀ Y : SchemeOverField k, T.IsSmoothProjective (ULiftHom.up.obj Y) →
        Function.Bijective
          (T.pullbackGrade
            (ULiftHom.up.map
              (AlgebraicGeometry.SchemeOverField.toGlobalSectionsSpec Y)) (0, 0)))
