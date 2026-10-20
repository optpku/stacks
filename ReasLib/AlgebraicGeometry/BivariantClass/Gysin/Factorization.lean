module

public import ReasLib.AlgebraicGeometry.BivariantClass.Gysin.RegularImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.RelativeDimensionLocus
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalCompleteIntersection

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass.Gysin

open Scheme.Hom Scheme.Hom.VirtualNormalBundle

/-- The common source locus of normal rank `r` and smooth relative dimension `t` in an
immersion–smooth factorization. -/
def factorizationRankLoci {S : Scheme.{u}} {X P Y : Over S}
    (i : X ⟶ P) (g : P ⟶ Y) [IsRegularImmersion i.left] [Smooth g.left]
    (e : Scheme.Modules.dual (normalSheaf i.left) ≅ conormalSheaf i.left)
    (rt : ℕ × ℕ) : X.left.Opens :=
  rankOpen i.left (normalBundle i.left e) rt.1 ⊓
    i.left ⁻¹ᵁ smoothRelativeDimensionLocus g.left rt.2

/-- The common normal-rank and smooth-dimension loci cover the source. -/
theorem factorizationRankLoci_iSup {S : Scheme.{u}} {X P Y : Over S}
    (i : X ⟶ P) (g : P ⟶ Y) [IsRegularImmersion i.left] [Smooth g.left]
    (e : Scheme.Modules.dual (normalSheaf i.left) ≅ conormalSheaf i.left) :
    iSup (factorizationRankLoci i g e) = ⊤ := sorry

/-- Distinct common normal-rank and smooth-dimension loci are disjoint. -/
theorem factorizationRankLoci_pairwiseDisjoint {S : Scheme.{u}} {X P Y : Over S}
    (i : X ⟶ P) (g : P ⟶ Y) [IsRegularImmersion i.left] [Smooth g.left]
    (e : Scheme.Modules.dual (normalSheaf i.left) ≅ conormalSheaf i.left) :
    Pairwise (fun rt su : ℕ × ℕ ↦ Disjoint
      (factorizationRankLoci i g e rt : Set X.left)
      (factorizationRankLoci i g e su : Set X.left)) := sorry

/-- Each common normal-rank and smooth-dimension locus is clopen. -/
theorem factorizationRankLoci_isClopen {S : Scheme.{u}} {X P Y : Over S}
    (i : X ⟶ P) (g : P ⟶ Y) [IsRegularImmersion i.left] [Smooth g.left]
    (e : Scheme.Modules.dual (normalSheaf i.left) ≅ conormalSheaf i.left)
    (rt : ℕ × ℕ) : IsClopen (factorizationRankLoci i g e rt : Set X.left) :=
  (@Scheme.Modules.rankClopen X.left (normalBundle i.left e).module
    (normalBundle i.left e).isFiniteLocallyFree rt.1).isClopen.inter
    ((smoothRelativeDimensionLocus_isClopen g.left rt.2).preimage i.left.continuous)

/-- On a common rank/dimension locus, the factorization class is the restricted normal
Gysin class followed by smooth flat pullback. -/
def factorizationComponent
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y P : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType P.hom] (f : X ⟶ Y) (i : X ⟶ P) (g : P ⟶ Y)
    [IsRegularImmersion i.left] [Smooth g.left] (hfac : i ≫ g = f)
    (e : Scheme.Modules.dual (normalSheaf i.left) ≅ conormalSheaf i.left)
    (D : ClosedDeformation X.hom (i.left.coborderRange.ι ≫ P.hom)
      i.left.liftCoborder
      (by rw [← Category.assoc, i.left.liftCoborder_ι]; exact Over.w i)
      (normalBundle i.left e).toCoborder)
    (rt : ℕ × ℕ) :
    BivariantClass δ
      (ComponentRestriction.hom f (factorizationRankLoci i g e rt) ⊤ (by simp))
      ((rt.1 : ℤ) - (rt.2 : ℤ)) := by
  have c := @comp S inferInstance δ inferInstance
    (ComponentRestriction.over X (factorizationRankLoci i g e rt))
    (ComponentRestriction.over P (smoothRelativeDimensionLocus g.left rt.2))
    (ComponentRestriction.over Y ⊤)
    (ComponentRestriction.locallyOfFiniteTypeOver X _)
    (ComponentRestriction.locallyOfFiniteTypeOver P _)
    (ComponentRestriction.locallyOfFiniteTypeOver Y _)
    (ComponentRestriction.hom i (factorizationRankLoci i g e rt)
      (smoothRelativeDimensionLocus g.left rt.2) inf_le_right)
    (ComponentRestriction.hom g (smoothRelativeDimensionLocus g.left rt.2) ⊤ (by simp))
    (rt.1 : ℤ) (-(rt.2 : ℤ))
    (ComponentRestriction.restrict δ i (rt.1 : ℤ)
      (factorizationRankLoci i g e rt) (smoothRelativeDimensionLocus g.left rt.2)
      inf_le_right (immersionClassDegree δ i e D rt.1))
    (@flatPullback S inferInstance δ inferInstance
      (ComponentRestriction.over P (smoothRelativeDimensionLocus g.left rt.2))
      (ComponentRestriction.over Y ⊤)
      (ComponentRestriction.locallyOfFiniteTypeOver P _)
      (ComponentRestriction.locallyOfFiniteTypeOver Y _)
      (ComponentRestriction.hom g (smoothRelativeDimensionLocus g.left rt.2) ⊤ (by simp))
      rt.2 (by change Flat (g.left.resLE _ _ _); infer_instance)
      (relativeDimension_smoothRelativeDimensionLocus g.left rt.2))
  have hcomp : ComponentRestriction.hom i (factorizationRankLoci i g e rt)
      (smoothRelativeDimensionLocus g.left rt.2) inf_le_right ≫
      ComponentRestriction.hom g (smoothRelativeDimensionLocus g.left rt.2) ⊤
        (by simp) =
      ComponentRestriction.hom f (factorizationRankLoci i g e rt) ⊤ (by simp) := by
    apply Over.OverMorphism.ext
    change i.left.resLE _ _ _ ≫ g.left.resLE _ _ _ = f.left.resLE _ _ _
    rw [Scheme.Hom.resLE_comp_resLE]
    have h : i.left ≫ g.left = f.left := congrArg (fun k : X ⟶ Y ↦ k.left) hfac
    simp only [h]
  rw [hcomp] at c
  exact c

/-- The degree-`p` component on a rank/dimension locus is the geometric factorization
class when its virtual degree is `p`, and is zero otherwise. -/
def factorizationComponentDegree
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y P : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType P.hom] (f : X ⟶ Y) (i : X ⟶ P) (g : P ⟶ Y)
    [IsRegularImmersion i.left] [Smooth g.left] (hfac : i ≫ g = f)
    (e : Scheme.Modules.dual (normalSheaf i.left) ≅ conormalSheaf i.left)
    (D : ClosedDeformation X.hom (i.left.coborderRange.ι ≫ P.hom)
      i.left.liftCoborder
      (by rw [← Category.assoc, i.left.liftCoborder_ι]; exact Over.w i)
      (normalBundle i.left e).toCoborder)
    (p : ℤ) (rt : ℕ × ℕ) :
    BivariantClass δ
      (ComponentRestriction.hom f (factorizationRankLoci i g e rt) ⊤ (by simp)) p :=
  if h : (rt.1 : ℤ) - (rt.2 : ℤ) = p then
    h ▸ factorizationComponent δ f i g hfac e D rt
  else pointwiseZero δ
    (ComponentRestriction.hom f (factorizationRankLoci i g e rt) ⊤ (by simp)) p

/-- The degree-`p` Gysin coefficient of an immersion–smooth factorization is assembled
from its geometric classes on the disjoint normal-rank and smooth-dimension loci. -/
def factorizationClassDegree
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y P : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType P.hom] (f : X ⟶ Y) (i : X ⟶ P) (g : P ⟶ Y)
    [IsRegularImmersion i.left] [Smooth g.left] (hfac : i ≫ g = f)
    (e : Scheme.Modules.dual (normalSheaf i.left) ≅ conormalSheaf i.left)
    (D : ClosedDeformation X.hom (i.left.coborderRange.ι ≫ P.hom)
      i.left.liftCoborder
      (by rw [← Category.assoc, i.left.liftCoborder_ι]; exact Over.w i)
      (normalBundle i.left e).toCoborder)
    (p : ℤ) : BivariantClass δ f p :=
  ComponentRestriction.assemble δ f p (factorizationRankLoci i g e)
    (fun _ : Unit ↦ ⊤) (fun _ ↦ Unit.unit)
    (factorizationRankLoci_iSup i g e) (by simp)
    (factorizationRankLoci_pairwiseDisjoint i g e)
    (by intro a b h; exact (h (Subsingleton.elim a b)).elim)
    (factorizationRankLoci_isClopen i g e) (fun _ ↦ isClopen_univ) (fun _ ↦ by simp)
    (factorizationComponentDegree δ f i g hfac e D p)

/-- Restricting the assembled factorization coefficient to a common rank/dimension locus
recovers the geometric coefficient on that locus. -/
theorem factorizationClassDegree_component
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y P : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType P.hom] (f : X ⟶ Y) (i : X ⟶ P) (g : P ⟶ Y)
    [IsRegularImmersion i.left] [Smooth g.left] (hfac : i ≫ g = f)
    (e : Scheme.Modules.dual (normalSheaf i.left) ≅ conormalSheaf i.left)
    (D : ClosedDeformation X.hom (i.left.coborderRange.ι ≫ P.hom)
      i.left.liftCoborder
      (by rw [← Category.assoc, i.left.liftCoborder_ι]; exact Over.w i)
      (normalBundle i.left e).toCoborder)
    (p : ℤ) (rt : ℕ × ℕ) :
    ComponentRestriction.restrict δ f p (factorizationRankLoci i g e rt) ⊤ (by simp)
        (factorizationClassDegree δ f i g hfac e D p) =
      factorizationComponentDegree δ f i g hfac e D p rt := sorry

end AlgebraicGeometry.BivariantClass.Gysin

namespace AlgebraicGeometry.BivariantClass

open Scheme.Hom Scheme.Hom.VirtualNormalBundle Gysin

/-- The integer-degree Gysin coefficients of a local complete intersection morphism
are independent of its regular-immersion–smooth factorization and deformation realization. -/
theorem gysin_eq_of_factorization
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [LocallyOfType RingHom.IsLocalCompleteIntersection f.left]
    {P : Over S} [LocallyOfFiniteType P.hom]
    (i : X ⟶ P) (g : P ⟶ Y) [IsRegularImmersion i.left] [Smooth g.left]
    (hfac : i ≫ g = f)
    (e : Scheme.Modules.dual (normalSheaf i.left) ≅ conormalSheaf i.left)
    (D : ClosedDeformation X.hom (i.left.coborderRange.ι ≫ P.hom)
      i.left.liftCoborder
      (by rw [← Category.assoc, i.left.liftCoborder_ι]; exact Over.w i)
      (normalBundle i.left e).toCoborder)
    {P' : Over S} [LocallyOfFiniteType P'.hom]
    (i' : X ⟶ P') (g' : P' ⟶ Y) [IsRegularImmersion i'.left] [Smooth g'.left]
    (hfac' : i' ≫ g' = f)
    (e' : Scheme.Modules.dual (normalSheaf i'.left) ≅ conormalSheaf i'.left)
    (D' : ClosedDeformation X.hom (i'.left.coborderRange.ι ≫ P'.hom)
      i'.left.liftCoborder
      (by rw [← Category.assoc, i'.left.liftCoborder_ι]; exact Over.w i')
      (normalBundle i'.left e').toCoborder) :
    (fun p : ℤ ↦ factorizationClassDegree δ f i g hfac e D p) =
      (fun p : ℤ ↦ factorizationClassDegree δ f i' g' hfac' e' D' p) := sorry

end AlgebraicGeometry.BivariantClass
