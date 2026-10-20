module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.Kunneth
public import ReasLib.AlgebraicGeometry.Scheme.Module.DescentLocus.Cohomology
public import ReasLib.CategoryTheory.Limits.Shapes.Pullback.Sections

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry
namespace Scheme

namespace TripleProduct

/-- The compatibility condition for the face map induced by a section of `f : X ⟶ S`. -/
theorem firstSection_condition {X Y Z S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (k : Z ⟶ S) (σ : SplitEpi f) :
    (pullback.fst g k ≫ (σ.pullbackSnd g).section_) ≫
        (pullback.fst f g ≫ f) = pullback.snd g k ≫ k := sorry

/-- The map `x × id_Y × id_Z` into the chosen nested triple fibre product,
induced by a chosen section `x` of `f : X ⟶ S`. -/
def firstSection {X Y Z S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (k : Z ⟶ S) (σ : SplitEpi f) :
    pullback g k ⟶ pullback (pullback.fst f g ≫ f) k :=
  pullback.lift (pullback.fst g k ≫ (σ.pullbackSnd g).section_)
    (pullback.snd g k) (firstSection_condition f g k σ)

/-- The first projection of `firstSection` is the section-induced map into `X ×[S] Y`. -/
theorem firstSection_fst {X Y Z S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (k : Z ⟶ S) (σ : SplitEpi f) :
    firstSection f g k σ ≫ pullback.fst (pullback.fst f g ≫ f) k =
      pullback.fst g k ≫ (σ.pullbackSnd g).section_ := sorry

/-- The second projection of `firstSection` is the projection to `Z`. -/
theorem firstSection_snd {X Y Z S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (k : Z ⟶ S) (σ : SplitEpi f) :
    firstSection f g k σ ≫ pullback.snd (pullback.fst f g ≫ f) k =
      pullback.snd g k := sorry

/-- The compatibility condition for the face map induced by a section of `g : Y ⟶ S`. -/
theorem secondSection_condition {X Y Z S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (k : Z ⟶ S) (τ : SplitEpi g) :
    (pullback.fst f k ≫ (τ.pullbackFst f).section_) ≫
        (pullback.fst f g ≫ f) = pullback.snd f k ≫ k := sorry

/-- The map `id_X × y × id_Z` into the chosen nested triple fibre product,
induced by a chosen section `y` of `g : Y ⟶ S`. -/
def secondSection {X Y Z S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (k : Z ⟶ S) (τ : SplitEpi g) :
    pullback f k ⟶ pullback (pullback.fst f g ≫ f) k :=
  pullback.lift (pullback.fst f k ≫ (τ.pullbackFst f).section_)
    (pullback.snd f k) (secondSection_condition f g k τ)

/-- The first projection of `secondSection` is the section-induced map into `X ×[S] Y`. -/
theorem secondSection_fst {X Y Z S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (k : Z ⟶ S) (τ : SplitEpi g) :
    secondSection f g k τ ≫ pullback.fst (pullback.fst f g ≫ f) k =
      pullback.fst f k ≫ (τ.pullbackFst f).section_ := sorry

/-- The second projection of `secondSection` is the projection to `Z`. -/
theorem secondSection_snd {X Y Z S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (k : Z ⟶ S) (τ : SplitEpi g) :
    secondSection f g k τ ≫ pullback.snd (pullback.fst f g ≫ f) k =
      pullback.snd f k := sorry

end TripleProduct

namespace Modules
namespace Invertible

/-- Let `f : X ⟶ S` and `g : Y ⟶ S` be flat, proper, finitely presented morphisms
whose structure-sheaf units are isomorphisms after every base change, and let both
morphisms have chosen sections. An invertible module on `pullback f g` that is trivial
along both section-induced maps and on the fiber over `s` is trivial over the inverse
image of some open neighborhood of `s`. -/
@[stacks 0BF3]
theorem isTrivial_near_of_sections_and_fiber
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [Flat f] [IsProper f] [Scheme.Hom.FinitePresentation f]
    [Flat g] [IsProper g] [Scheme.Hom.FinitePresentation g]
    (h_unit_f : ∀ {T : Scheme.{u}} (h : T ⟶ S),
      IsIso (SheafOfModules.unitToPushforwardObjUnit
        (pullback.snd f h).toRingCatSheafHom))
    (h_unit_g : ∀ {T : Scheme.{u}} (h : T ⟶ S),
      IsIso (SheafOfModules.unitToPushforwardObjUnit
        (pullback.snd g h).toRingCatSheafHom))
    (σ : SplitEpi f) (τ : SplitEpi g) (s : S)
    (L : (CategoryTheory.Limits.pullback f g).Modules) [Invertible L]
    (h_trivial_fst : RingedSpace.IsTrivial
      ((Scheme.Modules.pullback (τ.pullbackFst f).section_).obj L))
    (h_trivial_snd : RingedSpace.IsTrivial
      ((Scheme.Modules.pullback (σ.pullbackSnd g).section_).obj L))
    (h_trivial_fiber : RingedSpace.IsTrivial
      ((Scheme.Modules.pullback ((pullback.fst f g ≫ f).fiberι s)).obj L)) :
    ∃ U : S.Opens, s ∈ U ∧ RingedSpace.IsTrivial
      ((Scheme.Modules.pullback
        (pullback.fst (pullback.fst f g ≫ f) U.ι)).obj L) := sorry

/-- An invertible module on `X ×[S] Y ×[S] Z` is trivial if its two section-face
restrictions and one `Z`-fibre restriction are trivial, provided the first two
factors satisfy the stated geometric hypotheses and `Z` is connected. -/
@[stacks 0BF4]
theorem isTrivial_of_cube {X Y Z S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (k : Z ⟶ S) [Flat f] [IsProper f] [Scheme.Hom.FinitePresentation f]
    [GeometricallyIntegral f] [Flat g] [IsProper g]
    [Scheme.Hom.FinitePresentation g] [GeometricallyIntegral g] [ConnectedSpace Z]
    (x : SplitEpi f) (y : SplitEpi g) (z : Z)
    (L : (CategoryTheory.Limits.pullback (pullback.fst f g ≫ f) k).Modules)
    [Invertible L]
    (h_first : RingedSpace.IsTrivial
      ((Scheme.Modules.pullback (TripleProduct.firstSection f g k x)).obj L))
    (h_second : RingedSpace.IsTrivial
      ((Scheme.Modules.pullback (TripleProduct.secondSection f g k y)).obj L))
    (h_fibre : RingedSpace.IsTrivial
      ((Scheme.Modules.pullback
        ((pullback.snd (pullback.fst f g ≫ f) k).fiberι z)).obj L)) :
    RingedSpace.IsTrivial L := sorry

end Invertible
end Modules
end Scheme
end AlgebraicGeometry
