module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.AlgebraSheaf.ExteriorPower
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.Derived
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.RHom.IdealQuotient.Duality
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.StructureSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.ClosedImmersion.InternalHom
public import ReasLib.AlgebraicGeometry.Scheme.Module.Normal
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.RankLocus
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open DerivedCategory RingedSpace

noncomputable section

universe u

namespace AlgebraicGeometry.IsKoszulRegularClosedImmersion

/-- The normal sheaf of a Koszul-regular closed immersion is finite locally free. -/
theorem normalSheaf_isFiniteLocallyFree {X Y : Scheme.{u}} (i : X ⟶ Y)
    [IsKoszulRegularClosedImmersion i] :
    Scheme.Modules.IsFiniteLocallyFree (Scheme.Hom.normalSheaf i) := sorry

end AlgebraicGeometry.IsKoszulRegularClosedImmersion

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}}

/-- The degree-zero `r`th exterior power of the normal sheaf, shifted by `-r`, has
quasicoherent cohomology. -/
theorem normalExteriorShift_mem (i : X ⟶ Y)
    (h : Scheme.Modules.IsFiniteLocallyFree (normalSheaf i)) (r : ℕ) :
    Scheme.ModuleDerived.quasicoherentProperty X
      (((singleFunctor X.Modules 0).obj
        (ExteriorPower.sheaf (normalSheaf i) r))⟦(-(r : ℤ))⟧) := sorry

/-- The `r`th exterior power of the normal sheaf, placed in degree zero and shifted by
`-r`, as a quasicoherent derived object. -/
noncomputable def normalExteriorShift (i : X ⟶ Y)
    (h : Scheme.Modules.IsFiniteLocallyFree (normalSheaf i)) (r : ℕ) :
    Scheme.DerivedQCoh X :=
  ⟨((singleFunctor X.Modules 0).obj
      (ExteriorPower.sheaf (normalSheaf i) r))⟦(-(r : ℤ))⟧,
    normalExteriorShift_mem i h r⟩

/-- The underlying derived module of `normalExteriorShift i r` is the explicit shifted
degree-zero exterior power of the normal sheaf. -/
theorem normalExteriorShift_obj (i : X ⟶ Y)
    (h : Scheme.Modules.IsFiniteLocallyFree (normalSheaf i)) (r : ℕ) :
    (normalExteriorShift i h r).obj =
      ((singleFunctor X.Modules 0).obj
        (ExteriorPower.sheaf (normalSheaf i) r))⟦(-(r : ℤ))⟧ := sorry

/-- A quasicoherent derived object has the normal-exterior-shift form when, on each
canonical clopen rank locus, it is isomorphic to the corresponding fixed-rank object. -/
def IsNormalExteriorShift (i : X ⟶ Y)
    (h : Scheme.Modules.IsFiniteLocallyFree (normalSheaf i))
    (E : Scheme.DerivedQCoh X) : Prop :=
  ∀ r : ℕ, IsIsomorphic
    ((moduleRestrictionToOpenDerived X.toRingedSpace
      (Scheme.Modules.rankClopen (normalSheaf i) r).toOpens).obj
        (normalExteriorShift i h r).obj)
    ((moduleRestrictionToOpenDerived X.toRingedSpace
      (Scheme.Modules.rankClopen (normalSheaf i) r).toOpens).obj E.obj)

/-- The normal-exterior-shift property is exactly the family of isomorphisms on the
canonical clopen rank loci. -/
theorem isNormalExteriorShift_iff (i : X ⟶ Y)
    (h : Scheme.Modules.IsFiniteLocallyFree (normalSheaf i))
    (E : Scheme.DerivedQCoh X) :
    IsNormalExteriorShift i h E ↔
      ∀ r : ℕ, IsIsomorphic
        ((moduleRestrictionToOpenDerived X.toRingedSpace
          (Scheme.Modules.rankClopen (normalSheaf i) r).toOpens).obj
            (normalExteriorShift i h r).obj)
        ((moduleRestrictionToOpenDerived X.toRingedSpace
          (Scheme.Modules.rankClopen (normalSheaf i) r).toOpens).obj E.obj) := sorry

namespace IsNormalExteriorShift

/-- The normal-exterior-shift property is invariant under isomorphism of quasicoherent
derived objects. -/
theorem of_isIsomorphic (i : X ⟶ Y)
    (hFLF : Scheme.Modules.IsFiniteLocallyFree (normalSheaf i))
    {E F : Scheme.DerivedQCoh X} (hE : IsNormalExteriorShift i hFLF E)
    (h : IsIsomorphic E F) : IsNormalExteriorShift i hFLF F := sorry

end IsNormalExteriorShift

/-- If the normal sheaf has constant rank `r`, the rank-locus formulation is equivalent
to a global isomorphism with the fixed-rank normal exterior shift. -/
theorem isNormalExteriorShift_iff_of_rank (i : X ⟶ Y) (r : ℕ)
    (hFLF : Scheme.Modules.IsFiniteLocallyFree (normalSheaf i))
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r (normalSheaf i)]
    (E : Scheme.DerivedQCoh X) :
    IsNormalExteriorShift i hFLF E ↔ IsIsomorphic (normalExteriorShift i hFLF r) E := sorry

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- A chosen right adjoint to derived pushforward along a Koszul-regular closed immersion
sends the structure sheaf to a normal exterior shift. -/
theorem rightAdjointStructureSheaf_isNormalExteriorShift
    {X Y : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y]
    (i : X ⟶ Y) [IsKoszulRegularClosedImmersion i]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X)
    (aAdjunction : pushforwardCohomologyIn i ⊣ a) :
    Scheme.Hom.IsNormalExteriorShift i
      (IsKoszulRegularClosedImmersion.normalSheaf_isFiniteLocallyFree i)
      (a.obj (structureSheaf Y)) := sorry

/-- Under a constant-rank hypothesis, the right-adjoint image of the structure sheaf is
globally isomorphic to the corresponding fixed-rank normal exterior shift. -/
theorem normalExteriorShift_isomorphic_rightAdjointStructureSheaf_of_rank
    {X Y : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y]
    (i : X ⟶ Y) [IsKoszulRegularClosedImmersion i] (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r (Scheme.Hom.normalSheaf i)]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X)
    (aAdjunction : pushforwardCohomologyIn i ⊣ a) :
    IsIsomorphic
      (Scheme.Hom.normalExteriorShift i
        (IsKoszulRegularClosedImmersion.normalSheaf_isFiniteLocallyFree i) r)
      (a.obj (structureSheaf Y)) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
