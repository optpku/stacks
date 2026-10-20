/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ZariskiSite.Affine.Cover.Small
public import ReasLib.CategoryTheory.Sites.Derived.Sections.MayerVietoris

@[expose] public section

open CategoryTheory
open CategoryTheory.GrothendieckTopology.Derived.Sections.MayerVietoris
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.AffineZariski

/-- A Mayer--Vietoris square whose target is affine and whose two members are standard opens of
that target, with the overlap given by their intersection and the members covering the target. -/
def IsStandardOpenSquare {X : Scheme.{u}}
    (S : Square X.smallAffineZariskiSite) : Prop :=
  ∃ (U : X.affineOpens) (f g : Γ(X, U)),
    S.X.obj = (U : X.Opens) ∧
      S.Y.obj = (X.affineBasicOpen f : X.Opens) ∧
      S.Z.obj = (X.affineBasicOpen g : X.Opens) ∧
      S.E.obj = (X.affineBasicOpen (f * g) : X.Opens) ∧
      (U : X.Opens) =
        (X.affineBasicOpen f : X.Opens) ⊔ (X.affineBasicOpen g : X.Opens)

/-- The explicit geometric specification of a standard-open Mayer--Vietoris square. -/
theorem isStandardOpenSquare_iff {X : Scheme.{u}}
    (S : Square X.smallAffineZariskiSite) :
    IsStandardOpenSquare S ↔
      ∃ (U : X.affineOpens) (f g : Γ(X, U)),
        S.X.obj = (U : X.Opens) ∧
          S.Y.obj = (X.affineBasicOpen f : X.Opens) ∧
          S.Z.obj = (X.affineBasicOpen g : X.Opens) ∧
          S.E.obj = (X.affineBasicOpen (f * g) : X.Opens) ∧
          (U : X.Opens) =
            (X.affineBasicOpen f : X.Opens) ⊔ (X.affineBasicOpen g : X.Opens) := sorry

/-- The standard-open Mayer--Vietoris square attached to an affine open and two sections. -/
def standardOpenSquare (X : Scheme.{u}) (U : X.affineOpens) (f g : Γ(X, U)) :
    Square X.smallAffineZariskiSite :=
  let UX : X.smallAffineZariskiSite := ⟨(U : X.Opens), U.property⟩
  let Y : X.smallAffineZariskiSite :=
    ⟨(X.affineBasicOpen f : X.Opens), (X.affineBasicOpen f).property⟩
  let Z : X.smallAffineZariskiSite :=
    ⟨(X.affineBasicOpen g : X.Opens), (X.affineBasicOpen g).property⟩
  let E : X.smallAffineZariskiSite :=
    ⟨(X.affineBasicOpen (f * g) : X.Opens), (X.affineBasicOpen (f * g)).property⟩
  { E := E
    Y := Y
    Z := Z
    X := UX
    toY := ObjectProperty.homMk (homOfLE (show
        (X.affineBasicOpen (f * g) : X.Opens) ≤
          (X.affineBasicOpen f : X.Opens) by
      rw [show (X.affineBasicOpen (f * g) : X.Opens) =
        X.basicOpen (f * g) by rfl, X.basicOpen_mul]
      exact inf_le_left))
    toZ := ObjectProperty.homMk (homOfLE (show
        (X.affineBasicOpen (f * g) : X.Opens) ≤
          (X.affineBasicOpen g : X.Opens) by
      rw [show (X.affineBasicOpen (f * g) : X.Opens) =
        X.basicOpen (f * g) by rfl, X.basicOpen_mul]
      exact inf_le_right))
    inY := ObjectProperty.homMk (homOfLE (X.affineBasicOpen_le f))
    inZ := ObjectProperty.homMk (homOfLE (X.affineBasicOpen_le g))
    comm := by
      apply ObjectProperty.hom_ext
      rfl }

/-- The standard-open square satisfies the standard-open square predicate exactly when its two
basic opens cover the chosen affine target. -/
theorem isStandardOpenSquare_standardOpenSquare_iff (X : Scheme.{u}) (U : X.affineOpens)
    (f g : Γ(X, U)) :
    IsStandardOpenSquare (standardOpenSquare X U f g) ↔
      (U : X.Opens) =
        (X.affineBasicOpen f : X.Opens) ⊔ (X.affineBasicOpen g : X.Opens) := sorry

end AlgebraicGeometry.Scheme.AffineZariski

end
