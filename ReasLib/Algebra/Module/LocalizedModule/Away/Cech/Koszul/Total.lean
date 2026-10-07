module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Cech.Alternating.Functor
public import ReasLib.Algebra.Module.LocalizedModule.Away.Cech.Koszul.Hom

/-!
# Total powered-Koszul Hom-colimit comparison

This module makes the powered-Koszul Hom system functorial in its coefficient module and
compares its totalized colimit with the Cech-first total alternating Cech complex.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape HomologicalComplex₂

noncomputable section

universe u

namespace LocalizedModule.Away.Cech.Koszul

variable {A : Type u} [CommRing A] {r : ℕ}

/-- Coefficient postcomposition respects identity morphisms on the powered-Koszul Hom system. -/
theorem homSystemMap_id (f : Fin r → A) (M : ModuleCat.{u, u} A) :
    homSystemMap f (𝟙 M) = 𝟙 (homSystem f M) := sorry

/-- Coefficient postcomposition respects composition on the powered-Koszul Hom system. -/
theorem homSystemMap_comp (f : Fin r → A) {M N P : ModuleCat.{u, u} A}
    (g : M ⟶ N) (h : N ⟶ P) :
    homSystemMap f (g ≫ h) = homSystemMap f g ≫ homSystemMap f h := sorry

/-- The direct system of powered-Koszul Hom complexes, functorial in its coefficient module. -/
noncomputable def homSystemFunctor (f : Fin r → A) :
    ModuleCat.{u, u} A ⥤ (ℕ ⥤ CochainComplex (ModuleCat.{u, u} A) ℕ) where
  obj M := homSystem f M
  map g := homSystemMap f g
  map_id M := homSystemMap_id f M
  map_comp g h := homSystemMap_comp f g h

/-- Evaluating the powered-Koszul Hom-system functor gives the direct Hom system. -/
theorem homSystemFunctor_obj (f : Fin r → A) (M : ModuleCat.{u, u} A) :
    (homSystemFunctor f).obj M = homSystem f M := sorry

/-- Taking the sequential colimit of the powered-Koszul Hom system and extending by zero
from natural to integer degrees gives the functorial Hom row. -/
noncomputable def homColimitRow (f : Fin r → A) :
    ModuleCat.{u, u} A ⥤ CochainComplex (ModuleCat.{u, u} A) ℤ :=
  homSystemFunctor f ⋙ colim ⋙
    ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u, u} A)

/-- The powered-Koszul Hom-colimit row is the extended sequential colimit of the direct
Hom system. -/
theorem homColimitRow_obj (f : Fin r → A) (M : ModuleCat.{u, u} A) :
    (homColimitRow f).obj M =
      (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u, u} A)).obj
        (colimit (homSystem f M)) := sorry

/-- The powered-Koszul Hom-colimit row preserves zero morphisms. -/
instance homColimitRow_preservesZeroMorphisms (f : Fin r → A) :
    (homColimitRow f).PreservesZeroMorphisms := sorry

/-- Extending the canonical Hom-colimit comparison by zero identifies it with the
alternating-Cech row. -/
noncomputable def homColimitRowComponentIso (f : Fin r → A)
    (M : ModuleCat.{u, u} A) :
    (homColimitRow f).obj M ≅ (Alternating.row f).obj M :=
  (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u, u} A)).mapIso
    (homColimitIso f M)

/-- The powered-Koszul Hom-colimit row comparison is natural in the coefficient module. -/
theorem homColimitRowComponentIso_naturality (f : Fin r → A)
    {M N : ModuleCat.{u, u} A} (g : M ⟶ N) :
    (homColimitRow f).map g ≫ (homColimitRowComponentIso f N).hom =
      (homColimitRowComponentIso f M).hom ≫ (Alternating.row f).map g := sorry

/-- The powered-Koszul Hom-colimit row is naturally isomorphic to the alternating-Cech row. -/
noncomputable def homColimitRowIso (f : Fin r → A) :
    homColimitRow f ≅ Alternating.row f :=
  NatIso.ofComponents (homColimitRowComponentIso f)
    (homColimitRowComponentIso_naturality f)

/-- A component of the natural Hom-colimit row comparison is the extended canonical
degreewise comparison. -/
theorem homColimitRowIso_app (f : Fin r → A) (M : ModuleCat.{u, u} A) :
    (homColimitRowIso f).app M = homColimitRowComponentIso f M := sorry

/-- The total complex obtained by applying the powered-Koszul Hom-colimit row termwise to a
complex of coefficient modules. -/
noncomputable def homColimitTotal (f : Fin r → A) :
    CochainComplex (ModuleCat.{u, u} A) ℤ ⥤
      CochainComplex (ModuleCat.{u, u} A) ℤ :=
  (homColimitRow f).mapHomologicalComplex (up ℤ) ⋙
    totalFunctor (ModuleCat.{u, u} A) (up ℤ) (up ℤ) (up ℤ)

/-- Evaluating the powered-Koszul Hom-colimit total functor forms the total complex of the
termwise Hom colimits. -/
theorem homColimitTotal_obj (f : Fin r → A)
    (M : CochainComplex (ModuleCat.{u, u} A) ℤ) :
    (homColimitTotal f).obj M =
      HomologicalComplex₂.total
        (((homColimitRow f).mapHomologicalComplex (up ℤ)).obj M) (up ℤ) := sorry

/-- The powered-Koszul Hom-colimit total is naturally isomorphic to the Cech-first total
alternating Cech complex. -/
noncomputable def homColimitTotalIso (f : Fin r → A) :
    homColimitTotal f ≅ Alternating.total f :=
  Functor.isoWhiskerRight
      (NatIso.mapHomologicalComplex (homColimitRowIso f) (up ℤ))
      (totalFunctor (ModuleCat.{u, u} A) (up ℤ) (up ℤ) (up ℤ)) ≪≫
    Functor.isoWhiskerLeft
      ((Alternating.row f).mapHomologicalComplex (up ℤ))
      (totalFlipNatIso (C := ModuleCat.{u, u} A)
        (c₁ := up ℤ) (c₂ := up ℤ) (c := up ℤ)).symm

/-- A component of the total comparison first totalizes the row comparison and then applies
the inverse total-flip isomorphism. -/
theorem homColimitTotalIso_app (f : Fin r → A)
    (M : CochainComplex (ModuleCat.{u, u} A) ℤ) :
    (homColimitTotalIso f).app M =
      total.mapIso
          ((NatIso.mapHomologicalComplex (homColimitRowIso f) (up ℤ)).app M) (up ℤ) ≪≫
        (HomologicalComplex₂.totalFlipIso
          (((Alternating.row f).mapHomologicalComplex (up ℤ)).obj M) (up ℤ)).symm := sorry

/-- On a bidegree summand, the total comparison is the row comparison followed by the
flipped-total inclusion, multiplied by the sign `(-1)^(p*q)`. -/
theorem homColimitTotalIso_ι (f : Fin r → A)
    (M : CochainComplex (ModuleCat.{u, u} A) ℤ) (p q n : ℤ) (h : p + q = n) :
    HomologicalComplex₂.ιTotal
          (((homColimitRow f).mapHomologicalComplex (up ℤ)).obj M)
          (up ℤ) p q n h ≫
        ((homColimitTotalIso f).hom.app M).f n =
      (p * q).negOnePow •
        (((homColimitRowIso f).hom.app (M.X p)).f q ≫
          HomologicalComplex₂.ιTotal
            (HomologicalComplex₂.flip
              (((Alternating.row f).mapHomologicalComplex (up ℤ)).obj M))
            (up ℤ) q p n ((add_comm q p).trans h)) := sorry

end LocalizedModule.Away.Cech.Koszul

end
