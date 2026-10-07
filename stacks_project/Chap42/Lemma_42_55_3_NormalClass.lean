module

public import stacks_project.Chap42.Lemma_42_54_2_BivariantClass
public import ReasLib.AlgebraicGeometry.Scheme.Module.Normal

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle

/-- The normal sheaf has the same fixed finite rank as the conormal sheaf. -/
instance normalSheaf_isFiniteLocallyFreeOfRank {Z X : Scheme.{u}} (i : Z ⟶ X)
    (r : ℕ) [Scheme.Modules.IsFiniteLocallyFreeOfRank r (Scheme.Hom.conormalSheaf i)] :
    Scheme.Modules.IsFiniteLocallyFreeOfRank r (Scheme.Hom.normalSheaf i) := sorry

/-- The virtual normal bundle whose module is the normal sheaf and whose quotient map is a
chosen bidual identification with the conormal sheaf. -/
noncomputable def ofNormalSheaf {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (r : ℕ) [Scheme.Modules.IsFiniteLocallyFreeOfRank r (Scheme.Hom.conormalSheaf i)]
    (e : Scheme.Modules.dual (Scheme.Hom.normalSheaf i) ≅ Scheme.Hom.conormalSheaf i) :
    VirtualNormalBundle i :=
  ofSurjection i (Scheme.Hom.normalSheaf i)
    (Scheme.Modules.isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank
      r (Scheme.Hom.normalSheaf i)) e.hom inferInstance

/-- The module of `ofNormalSheaf` has the prescribed fixed finite rank. -/
instance ofNormalSheaf_module_isFiniteLocallyFreeOfRank
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (r : ℕ) [Scheme.Modules.IsFiniteLocallyFreeOfRank r (Scheme.Hom.conormalSheaf i)]
    (e : Scheme.Modules.dual (Scheme.Hom.normalSheaf i) ≅ Scheme.Hom.conormalSheaf i) :
    Scheme.Modules.IsFiniteLocallyFreeOfRank r (ofNormalSheaf i r e).module := sorry

/-- The module of `ofNormalSheaf` is the normal sheaf. -/
theorem ofNormalSheaf_module {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (r : ℕ) [Scheme.Modules.IsFiniteLocallyFreeOfRank r (Scheme.Hom.conormalSheaf i)]
    (e : Scheme.Modules.dual (Scheme.Hom.normalSheaf i) ≅ Scheme.Hom.conormalSheaf i) :
    (ofNormalSheaf i r e).module = Scheme.Hom.normalSheaf i := sorry

/-- The quotient map of `ofNormalSheaf` is the chosen bidual identification. -/
theorem ofNormalSheaf_map {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (r : ℕ) [Scheme.Modules.IsFiniteLocallyFreeOfRank r (Scheme.Hom.conormalSheaf i)]
    (e : Scheme.Modules.dual (Scheme.Hom.normalSheaf i) ≅ Scheme.Hom.conormalSheaf i) :
    (ofNormalSheaf i r e).map = e.hom := sorry

/-- The degree-`r` bivariant class of the normal sheaf, formed from explicit deformation to
the normal cone data. -/
noncomputable def normalClass
    {S Z X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (p : X ⟶ S) [LocallyOfFiniteType p]
    (i : Z ⟶ X) [LocallyOfFiniteType (i ≫ p)] [IsClosedImmersion i]
    (r : ℕ) [Scheme.Modules.IsFiniteLocallyFreeOfRank r (Scheme.Hom.conormalSheaf i)]
    (e : Scheme.Modules.dual (Scheme.Hom.normalSheaf i) ≅ Scheme.Hom.conormalSheaf i)
    (D : ClosedSpecialization delta (i ≫ p) p i rfl (ofNormalSheaf i r e)) :
    BivariantClass delta (overHom (i ≫ p) p i rfl) (r : ℤ) :=
  globalClassOfRank delta (i ≫ p) p i rfl (ofNormalSheaf i r e) D r

/-- The normal-sheaf class is the corresponding rank component of the virtual-normal class. -/
theorem normalClass_def
    {S Z X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (p : X ⟶ S) [LocallyOfFiniteType p]
    (i : Z ⟶ X) [LocallyOfFiniteType (i ≫ p)] [IsClosedImmersion i]
    (r : ℕ) [Scheme.Modules.IsFiniteLocallyFreeOfRank r (Scheme.Hom.conormalSheaf i)]
    (e : Scheme.Modules.dual (Scheme.Hom.normalSheaf i) ≅ Scheme.Hom.conormalSheaf i)
    (D : ClosedSpecialization delta (i ≫ p) p i rfl (ofNormalSheaf i r e)) :
    normalClass delta p i r e D =
      globalClassOfRank delta (i ≫ p) p i rfl (ofNormalSheaf i r e) D r := sorry

end AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle
