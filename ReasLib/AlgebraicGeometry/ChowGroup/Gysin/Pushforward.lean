module

public import ReasLib.AlgebraicGeometry.ChowGroup.FirstChern.Pushforward
public import ReasLib.AlgebraicGeometry.ChowGroup.Gysin
public import ReasLib.AlgebraicGeometry.ChowGroup.Gysin.TrivialRestriction
public import ReasLib.AlgebraicGeometry.Scheme.Module.ZeroScheme.Pullback.Over

/-!
# Proper pushforward and Gysin homomorphisms

This file records the compatibility of zero-scheme Gysin homomorphisms with proper
pushforward.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A trivial restriction of an invertible module to the zero scheme of a section
remains trivial on the zero scheme of the pulled-back section. -/
theorem isTrivial_zeroScheme_sectionsPullback
    {S : Scheme.{u}} {X X' : Over S} (f : X' ⟶ X)
    (ℒ : X.left.Modules) [Invertible ℒ] (s : ℒ.sections)
    (htriv : RingedSpace.IsTrivial ((pullback (zeroSchemeι ℒ s)).obj ℒ)) :
    RingedSpace.IsTrivial
      ((pullback
          (zeroSchemeι ((pullback f.left).obj ℒ) (sectionsPullback f.left ℒ s))).obj
        ((pullback f.left).obj ℒ)) := sorry

/-- Gysin pullback along the zero scheme of a section commutes with proper pushforward
from the corresponding pulled-back zero scheme. -/
theorem gysin_map_eq_map_gysin
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X X' : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType X'.hom]
    (f : X' ⟶ X) [IsProper f.left] (ℒ : X.left.Modules) [Invertible ℒ]
    (s : ℒ.sections) (k : ℤ)
    (α' : CycleGroup X'.left (X'.hom.relativeDimensionFunction δ) (k + 1)) :
    gysin X.hom δ ℒ s k
        (CycleGroup.mapHom f.left (X'.hom.relativeDimensionFunction δ)
          (X.hom.relativeDimensionFunction δ) (k + 1) α') =
      ChowGroup.map δ
        (Over.mk
          (zeroSchemeι ((pullback f.left).obj ℒ) (sectionsPullback f.left ℒ s) ≫ X'.hom))
        (Over.mk (zeroSchemeι ℒ s ≫ X.hom))
        (zeroSchemePullbackOverHom f ℒ s) k
        (gysin X'.hom δ ((pullback f.left).obj ℒ)
          (sectionsPullback f.left ℒ s) k α') := sorry

/-- For an invertible module whose restriction to the zero scheme of a section is
trivial, cycle-level Gysin commutes with proper pushforward along the induced
zero-scheme square over a universally catenary base with a dimension function. -/
theorem trivialGysin_map_eq_map_trivialGysin
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X X' : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType X'.hom]
    (f : X' ⟶ X) [IsProper f.left] (ℒ : X.left.Modules) [Invertible ℒ]
    (s : ℒ.sections)
    (htriv : RingedSpace.IsTrivial ((pullback (zeroSchemeι ℒ s)).obj ℒ))
    (k : ℤ) (α' : CycleGroup X'.left (X'.hom.relativeDimensionFunction δ) (k + 1)) :
    trivialGysin X.hom δ ℒ s htriv k
        (CycleGroup.mapHom f.left (X'.hom.relativeDimensionFunction δ)
          (X.hom.relativeDimensionFunction δ) (k + 1) α') =
      CycleGroup.mapHom (zeroSchemePullbackOverHom f ℒ s).left
        ((zeroSchemeι ((pullback f.left).obj ℒ)
            (sectionsPullback f.left ℒ s) ≫ X'.hom).relativeDimensionFunction δ)
        ((zeroSchemeι ℒ s ≫ X.hom).relativeDimensionFunction δ) k
        (trivialGysin X'.hom δ ((pullback f.left).obj ℒ)
          (sectionsPullback f.left ℒ s)
          (isTrivial_zeroScheme_sectionsPullback f ℒ s htriv) k α') := sorry

end AlgebraicGeometry.Scheme.Modules
