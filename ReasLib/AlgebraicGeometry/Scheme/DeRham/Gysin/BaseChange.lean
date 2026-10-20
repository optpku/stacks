module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.Gysin.ClosedImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.LocalCohomology.BaseChange

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham.Gysin.BaseChange

variable {Z' X' S' Z X S : Scheme.{u}}

open SheafOfModules.RingedSite.ExteriorPower

/-- The canonical quasicoherent morphism from pulled-back relative forms to relative forms for
a commutative square of schemes. -/
noncomputable def formMap {g : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {k : S' ⟶ S}
    (sq : CommSq g f' f k) (p : ℕ) :
    (Scheme.QCoh.pullback g).obj (Gysin.relativeFormQCoh f p) ⟶
      Gysin.relativeFormQCoh f' p :=
  ⟨eqToHom (Scheme.QCoh.pullback_obj g (Gysin.relativeFormQCoh f p)) ≫
    (Scheme.Modules.fromRingedSpace X').map
      (Scheme.RelativeDifferentials.formComparison sq p)⟩

/-- The underlying module morphism of `formMap` is the relative differential-form comparison,
after the canonical identification of quasicoherent pullback with module pullback. -/
theorem formMap_hom {g : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {k : S' ⟶ S}
    (sq : CommSq g f' f k) (p : ℕ) :
    (formMap sq p).hom =
      eqToHom (Scheme.QCoh.pullback_obj g (Gysin.relativeFormQCoh f p)) ≫
        (Scheme.Modules.fromRingedSpace X').map
          (Scheme.RelativeDifferentials.formComparison sq p) := sorry

/-- The outer commutative square obtained by vertically composing a closed-immersion square
with its ambient base square. -/
theorem outerSquare (h : Z' ⟶ Z) (i' : Z' ⟶ X') (i : Z ⟶ X)
    (g : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (k : S' ⟶ S)
    (sqZX : IsPullback h i' i g) (sqXS : CommSq g f' f k) :
    CommSq h (i' ≫ f') (i ≫ f) k := sorry

/-- The relative-form comparison for the outer rectangle of a closed-immersion square and
a commutative base square. -/
noncomputable def sourceFormMap (h : Z' ⟶ Z) (i' : Z' ⟶ X') (i : Z ⟶ X)
    (g : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (k : S' ⟶ S)
    (sqZX : IsPullback h i' i g) (sqXS : CommSq g f' f k) (p : ℕ) :
    (Scheme.Modules.pullback h).obj (sheaf Z.𝒪 Ω[(i ≫ f).toShHom] p) ⟶
      sheaf Z'.𝒪 Ω[(i' ≫ f').toShHom] p :=
  (Scheme.Modules.fromRingedSpace Z').map
    (Scheme.RelativeDifferentials.formComparison
      (outerSquare h i' i g f' f k sqZX sqXS) p)

/-- The outer relative-form map is induced by the canonical comparison for the vertically
composite square. -/
theorem sourceFormMap_def (h : Z' ⟶ Z) (i' : Z' ⟶ X') (i : Z ⟶ X)
    (g : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (k : S' ⟶ S)
    (sqZX : IsPullback h i' i g) (sqXS : CommSq g f' f k) (p : ℕ) :
    sourceFormMap h i' i g f' f k sqZX sqXS p =
      (Scheme.Modules.fromRingedSpace Z').map
        (Scheme.RelativeDifferentials.formComparison
          (outerSquare h i' i g f' f k sqZX sqXS) p) := sorry

/-- The left vertical comparison for Gysin base change: underived base change for the closed
immersion followed by functoriality of relative forms. -/
noncomputable def source (h : Z' ⟶ Z) (i' : Z' ⟶ X') (i : Z ⟶ X)
    (g : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (k : S' ⟶ S)
    (sqZX : IsPullback h i' i g) (sqXS : CommSq g f' f k) (p : ℕ) :
    (Scheme.Modules.pullback g).obj
        ((Scheme.Modules.toRingedSpace X).obj
          ((Scheme.Modules.pushforward i).obj
            (sheaf Z.𝒪 Ω[(i ≫ f).toShHom] p))) ⟶
      (Scheme.Modules.toRingedSpace X').obj
        ((Scheme.Modules.pushforward i').obj
          (sheaf Z'.𝒪 Ω[(i' ≫ f').toShHom] p)) :=
  (RingedSpace.Hom.BaseChange.map
      (sqZX.toCommSq.map
        (Scheme.forgetToLocallyRingedSpace ⋙
          LocallyRingedSpace.forgetToSheafedSpace))).app _ ≫
    (RingedSpace.Hom.pushforward i'.toShHom).map
      (sourceFormMap h i' i g f' f k sqZX sqXS p)

/-- The left vertical comparison is the underived base-change mate followed by the pushed
relative-form comparison for the outer square. -/
theorem source_def (h : Z' ⟶ Z) (i' : Z' ⟶ X') (i : Z ⟶ X)
    (g : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (k : S' ⟶ S)
    (sqZX : IsPullback h i' i g) (sqXS : CommSq g f' f k) (p : ℕ) :
    Gysin.BaseChange.source h i' i g f' f k sqZX sqXS p =
      (RingedSpace.Hom.BaseChange.map
        (sqZX.toCommSq.map
          (Scheme.forgetToLocallyRingedSpace ⋙
            LocallyRingedSpace.forgetToSheafedSpace))).app _ ≫
        (RingedSpace.Hom.pushforward i'.toShHom).map
          (sourceFormMap h i' i g f' f k sqZX sqXS p) := sorry

/-- The right vertical comparison for Gysin base change: local-cohomology base change followed
by functoriality of relative forms. -/
noncomputable def target (h : Z' ⟶ Z) (i' : Z' ⟶ X') (i : Z ⟶ X)
    (g : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (k : S' ⟶ S)
    [IsClosedImmersion i'] [IsClosedImmersion i] [Scheme.Hom.FinitePresentation i]
    (c p : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf i)]
    (sqZX : IsPullback h i' i g) (sqXS : CommSq g f' f k) :
    (Scheme.Modules.pullback g).obj
        ((Scheme.Hom.LocalCohomology.functor i c).obj
          (Gysin.relativeFormQCoh f (p + c))) ⟶
      (Scheme.Hom.LocalCohomology.functor i' c).obj
        (Gysin.relativeFormQCoh f' (p + c)) :=
  Scheme.Hom.LocalCohomology.BaseChange.map h i' i g c sqZX
      (Gysin.relativeFormQCoh f (p + c)) ≫
    (Scheme.Hom.LocalCohomology.functor i' c).map (formMap sqXS (p + c))

/-- The right vertical comparison is local-cohomology base change followed by the map on
coefficients induced by relative differential forms. -/
theorem target_def (h : Z' ⟶ Z) (i' : Z' ⟶ X') (i : Z ⟶ X)
    (g : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (k : S' ⟶ S)
    [IsClosedImmersion i'] [IsClosedImmersion i] [Scheme.Hom.FinitePresentation i]
    (c p : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf i)]
    (sqZX : IsPullback h i' i g) (sqXS : CommSq g f' f k) :
    target h i' i g f' f k c p sqZX sqXS =
      Scheme.Hom.LocalCohomology.BaseChange.map h i' i g c sqZX
          (Gysin.relativeFormQCoh f (p + c)) ≫
        (Scheme.Hom.LocalCohomology.functor i' c).map (formMap sqXS (p + c)) := sorry

end AlgebraicGeometry.Scheme.DeRham.Gysin.BaseChange

namespace AlgebraicGeometry.Scheme.DeRham.Gysin

/-- The Gysin morphism of a finitely presented closed immersion is natural under cartesian
base change when the canonical conormal comparison is an isomorphism. -/
theorem mapOfClosedImmersion_baseChange
    {Z' X' S' Z X S : Scheme.{u}}
    (h : Z' ⟶ Z) (i' : Z' ⟶ X') (i : Z ⟶ X) (g : X' ⟶ X)
    (f' : X' ⟶ S') (f : X ⟶ S) (k : S' ⟶ S)
    [IsClosedImmersion i'] [IsClosedImmersion i]
    [Scheme.Hom.FinitePresentation i'] [Scheme.Hom.FinitePresentation i]
    (c p : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf i')]
    [SheafOfModules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf i)]
    (sqZX : IsPullback h i' i g) (sqXS : CommSq g f' f k)
    [IsIso (Scheme.Hom.Conormal.map sqZX.toCommSq)] :
    CommSq
      ((Modules.pullback g).map (mapOfClosedImmersion i f c p))
      (BaseChange.source h i' i g f' f k sqZX sqXS p)
      (BaseChange.target h i' i g f' f k c p sqZX sqXS)
      (mapOfClosedImmersion i' f' c p) := sorry

end AlgebraicGeometry.Scheme.DeRham.Gysin

end
