/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.CategoryTheory.Abelian.LeftDerived
public import ReasLib.Algebra.Homology.HomologicalComplex.PreservesHomology

@[expose] public section
open CategoryTheory CategoryTheory.Limits
noncomputable section

namespace ActualExactLeftComposition
variable {A B C : Type*} [Category* A] [Category* B] [Category* C]
variable [Abelian A] [Abelian B] [Abelian C]
variable (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
variable {M : A} (P : ProjectiveResolution M) (Q : ProjectiveResolution (F.obj M))

/-- Apply the actual exact coefficient functor to a projective resolution. -/
abbrev complex : ChainComplex B ℕ := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex

/-- Exactness at the augmentation of the mapped projective resolution. -/
theorem exactZero :
    (ShortComplex.mk ((complex F P).d 1 0) (F.map (P.π.f 0)) (by
      change F.map (P.complex.d 1 0) ≫ F.map (P.π.f 0) = 0
      rw [← F.map_comp, P.complex_d_comp_π_f_zero, F.map_zero])).Exact := sorry

/-- Exactness in the positive degrees of the mapped projective resolution. -/
theorem exactSucc (n : ℕ) :
    (ShortComplex.mk ((complex F P).d (n + 2) (n + 1)) ((complex F P).d (n + 1) n)
      ((complex F P).d_comp_d (n + 2) (n + 1) n)).Exact := sorry

/-- The exact image of the augmentation is epic. -/
instance augmentation_epi : Epi (F.map (P.π.f 0)) := sorry

/-- The first lift uses the target project's actual projectivity against the mapped augmentation. -/
def zero : Q.complex.X 0 ⟶ (complex F P).X 0 :=
  @Projective.factorThru _ _ _ _ _ _ (Q.π.f 0) (F.map (P.π.f 0)) (augmentation_epi F P)

/-- The degree-one lift is the actual exactness/projectivity factorization. -/
def one : Q.complex.X 1 ⟶ (complex F P).X 1 :=
  (exactZero F P).liftFromProjective (Q.complex.d 1 0 ≫ zero F P Q) sorry

/-- The first two lift components commute with the differential. -/
theorem one_zero_comm : one F P Q ≫ (complex F P).d 1 0 = Q.complex.d 1 0 ≫ zero F P Q := sorry

/-- Successive chain components are explicitly lifted through the exact mapped resolution. -/
def succ (n : ℕ) (g : Q.complex.X n ⟶ (complex F P).X n)
    (g' : Q.complex.X (n + 1) ⟶ (complex F P).X (n + 1))
    (w : g' ≫ (complex F P).d (n + 1) n = Q.complex.d (n + 1) n ≫ g) :
    Σ' g'' : Q.complex.X (n + 2) ⟶ (complex F P).X (n + 2),
      g'' ≫ (complex F P).d (n + 2) (n + 1) = Q.complex.d (n + 2) (n + 1) ≫ g' :=
  ⟨(exactSucc F P n).liftFromProjective (Q.complex.d (n + 2) (n + 1) ≫ g') sorry, sorry⟩

/-- The actual comparison chain map, without asserting that restriction preserves projectives. -/
def map : Q.complex ⟶ complex F P :=
  ChainComplex.mkHom _ _ (zero F P Q) (one F P Q) (one_zero_comm F P Q)
    (fun n ⟨g, g', w⟩ ↦ ⟨(succ F P Q n g g' w).1, (succ F P Q n g g' w).2⟩)

variable [HasProjectiveResolutions A] [HasProjectiveResolutions B] (G : B ⥤ C) [G.Additive]

/-- The canonical left-derived composition map uses the specified projective comparison. -/
def app (M : A) (n : ℕ) : (G.leftDerived n).obj (F.obj M) ⟶ ((F ⋙ G).leftDerived n).obj M :=
  let P := projectiveResolution M
  let Q := projectiveResolution (F.obj M)
  (Q.isoLeftDerivedObj G n).hom ≫
    (HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) n).map
      ((G.mapHomologicalComplex (ComplexShape.down ℕ)).map (map F P Q) ≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (ComplexShape.down ℕ)).hom.app P.complex) ≫
    (P.isoLeftDerivedObj (F ⋙ G) n).inv

/-- Naturality follows from comparison homotopies of the actual chain lifts. -/
theorem app_naturality {M N : A} (a : M ⟶ N) (n : ℕ) :
    (G.leftDerived n).map (F.map a) ≫ app F G N n = app F G M n ≫ ((F ⋙ G).leftDerived n).map a := sorry

/-- The actual natural comparison from precomposition after derivation to derivation of the composite. -/
def comparison (n : ℕ) : F ⋙ G.leftDerived n ⟶ (F ⋙ G).leftDerived n where
  app M := app F G M n
  naturality := fun _ _ a ↦ app_naturality F G a n

/-- Acyclic images of source projectives make this specified comparison invertible. -/
theorem comparison_isIso
    (hacyclic : ∀ P : A, Projective P → ∀ n : ℕ, IsZero ((G.leftDerived (n + 1)).obj (F.obj P)))
    (n : ℕ) : IsIso (comparison F G n) := sorry

/-- Invert only the constructed map when its actual projective-acyclicity criterion holds. -/
def isoOfAcyclic
    (hacyclic : ∀ P : A, Projective P → ∀ n : ℕ, IsZero ((G.leftDerived (n + 1)).obj (F.obj P)))
    (n : ℕ) := @asIso _ _ _ _ (comparison F G n) (comparison_isIso F G hacyclic n)

end ActualExactLeftComposition

namespace ActualLeftDerived
variable {A B C : Type*} [Category* A] [Category* B] [Category* C]
variable [Abelian A] [Abelian B] [Abelian C] [HasProjectiveResolutions A]

/-- Derive the two actual directions of an underived natural isomorphism. -/
def mapIso {F G : A ⥤ B} [F.Additive] [G.Additive] (e : F ≅ G) (n : ℕ) :
    F.leftDerived n ≅ G.leftDerived n where
  hom := NatTrans.leftDerived e.hom n
  inv := NatTrans.leftDerived e.inv n
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Exact postcomposition is compared using the actual projective-resolution homology maps. -/
def postcompObjIso (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] [G.PreservesHomology]
    (n : ℕ) (M : A) : ((F ⋙ G).leftDerived n).obj M ≅ G.obj ((F.leftDerived n).obj M) :=
  let P := projectiveResolution M
  P.isoLeftDerivedObj (F ⋙ G) n ≪≫
    (HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) n).mapIso
      ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (ComplexShape.down ℕ)).symm.app P.complex) ≪≫
    ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).mapHomologyIso G n ≪≫
    G.mapIso (P.isoLeftDerivedObj F n).symm

/-- The exact-postcomposition isomorphism is natural for the specified maps. -/
def postcompIso (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] [G.PreservesHomology] (n : ℕ) :
    (F ⋙ G).leftDerived n ≅ F.leftDerived n ⋙ G :=
  NatIso.ofComponents (postcompObjIso F G n) (fun _ ↦ sorry)

end ActualLeftDerived
