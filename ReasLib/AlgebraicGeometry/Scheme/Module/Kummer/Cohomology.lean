/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Kummer.Classes
public import ReasLib.AlgebraicGeometry.Scheme.Module.Kummer.Torsor
public import ReasLib.CategoryTheory.Sites.Torsor.Cohomology

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.Kummer

variable (S : Scheme.{u}) (n : ℕ) (h_pos : 0 < n)
  (τ : StandardTopology) (hτ : AdmissibleTopology S n τ)
  [HasSheafify (τ.overTopology S) AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (τ.overTopology S) AddCommGrpCat.{u + 1})]

/-- An equipped pair determines the cohomology class of its compatible-trivialization torsor. -/
def pairClass (P : Pair S n) :
    (Sheaf.rootsOfUnityAddSheaf (AssociatedModule.bigCommStructureSheaf τ S) n).H 1 :=
  Sheaf.Torsor.Cohomology.classMap
    (Sheaf.rootsOfUnityAddSheaf (AssociatedModule.bigCommStructureSheaf τ S) n)
    (Quotient.mk'' (trivializationTorsor P h_pos τ hτ))

/-- Compatible-isomorphic equipped pairs determine the same torsor cohomology class. -/
theorem pairClass_congr {P Q : Pair S n} (e : PairIso P Q) :
    pairClass S n h_pos τ hτ P = pairClass S n h_pos τ hτ Q := sorry

/-- The torsor cohomology class descends to compatible-isomorphism classes of equipped pairs. -/
def classesToH1 : Classes S n →
    (Sheaf.rootsOfUnityAddSheaf (AssociatedModule.bigCommStructureSheaf τ S) n).H 1 :=
  Quotient.lift (pairClass S n h_pos τ hτ)
    (fun _ _ h ↦ h.elim (pairClass_congr S n h_pos τ hτ))

/-- The trivial equipped-pair class has zero torsor cohomology class. -/
theorem cohomologyMap_zero : classesToH1 S n h_pos τ hτ 0 = 0 := sorry

/-- Tensor products of equipped pairs add their torsor cohomology classes. -/
theorem cohomologyMap_add (x y : Classes S n) :
    classesToH1 S n h_pos τ hτ (x + y) =
      classesToH1 S n h_pos τ hτ x + classesToH1 S n h_pos τ hτ y := sorry

/-- The canonical additive homomorphism sends an equipped-pair class to its torsor class. -/
def cohomologyMap : Classes S n →+
    (Sheaf.rootsOfUnityAddSheaf (AssociatedModule.bigCommStructureSheaf τ S) n).H 1 where
  toFun := classesToH1 S n h_pos τ hτ
  map_zero' := cohomologyMap_zero S n h_pos τ hτ
  map_add' := cohomologyMap_add S n h_pos τ hτ

/-- Compatible-trivialization torsors classify first roots-of-unity cohomology bijectively. -/
theorem cohomologyMap_bijective :
    Function.Bijective (cohomologyMap S n h_pos τ hτ) := sorry

/-- First roots-of-unity cohomology is canonically the tensor-product group of equipped-pair classes. -/
def h1EquivClasses :
    (Sheaf.rootsOfUnityAddSheaf (AssociatedModule.bigCommStructureSheaf τ S) n).H 1 ≃+
      Classes S n :=
  (AddEquiv.ofBijective (cohomologyMap S n h_pos τ hτ)
    (cohomologyMap_bijective S n h_pos τ hτ)).symm

/-- The inverse classification sends a pair class to the class of its trivialization torsor. -/
theorem h1EquivClasses_symm_class (P : Pair S n) :
    (h1EquivClasses S n h_pos τ hτ).symm (classOf P) =
      Sheaf.Torsor.Cohomology.classMap
        (Sheaf.rootsOfUnityAddSheaf (AssociatedModule.bigCommStructureSheaf τ S) n)
        (Quotient.mk'' (trivializationTorsor P h_pos τ hτ)) := sorry

/-- Étale first roots-of-unity cohomology classifies equipped pairs when the exponent is invertible. -/
def h1EtaleEquivClasses (S : Scheme.{u}) (n : ℕ) (h_pos : 0 < n)
    [HasSheafify (StandardTopology.etale.overTopology S) AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf (StandardTopology.etale.overTopology S) AddCommGrpCat.{u + 1})]
    (h_n : IsUnit (n : Γ(S, ⊤))) :
    (Sheaf.rootsOfUnityAddSheaf (AssociatedModule.bigCommStructureSheaf .etale S) n).H 1 ≃+
      Classes S n :=
  h1EquivClasses S n h_pos .etale (Or.inr (Or.inr ⟨rfl, h_n⟩))

/-- Fppf first roots-of-unity cohomology classifies equipped pairs for every positive exponent. -/
def h1FppfEquivClasses (S : Scheme.{u}) (n : ℕ) (h_pos : 0 < n)
    [HasSheafify (StandardTopology.fppf.overTopology S) AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf (StandardTopology.fppf.overTopology S) AddCommGrpCat.{u + 1})] :
    (Sheaf.rootsOfUnityAddSheaf (AssociatedModule.bigCommStructureSheaf .fppf S) n).H 1 ≃+
      Classes S n :=
  h1EquivClasses S n h_pos .fppf (Or.inl rfl)

/-- Syntomic first roots-of-unity cohomology classifies equipped pairs for every positive exponent. -/
def h1SyntomicEquivClasses (S : Scheme.{u}) (n : ℕ) (h_pos : 0 < n)
    [HasSheafify (StandardTopology.syntomic.overTopology S) AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf (StandardTopology.syntomic.overTopology S) AddCommGrpCat.{u + 1})] :
    (Sheaf.rootsOfUnityAddSheaf (AssociatedModule.bigCommStructureSheaf .syntomic S) n).H 1 ≃+
      Classes S n :=
  h1EquivClasses S n h_pos .syntomic (Or.inr (Or.inl rfl))

end AlgebraicGeometry.Scheme.Modules.Kummer
