module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Line.Divisor
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.MorphismProperties
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections.RelativeRepresentability
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FunctionField.Units
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.SchemeTheoreticImage.FunctionField
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.SchemeTheoreticImage.Section
public import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RationalFunctionGraph

variable {S : Scheme.{u}} (X : Over S) (U : X.left.Opens) (s : Γ(X.left, U)ˣ)

/-- The affine-line morphism whose coordinate is the section `s` on `U`. -/
noncomputable def affineMap :
    U.toScheme ⟶ ProjectiveLine.affineLine (ULift.{u} ℤ) :=
  AffineSpace.homOfVector (specULiftZIsTerminal.from U.toScheme)
    (fun _ ↦ U.topIso.inv (s : Γ(X.left, U)))

/-- The affine coordinate of `affineMap X U s` is the transported section `s`. -/
theorem affineMap_coordinate :
    (affineMap X U s).appTop
        (AffineSpace.coord (Spec (CommRingCat.of (ULift.{u} ℤ)))
          (ULift.up (0 : Fin 1))) = U.topIso.inv (s : Γ(X.left, U)) := sorry

/-- The morphism from `U` to the integral projective line obtained through its `X`-chart. -/
noncomputable def integralSection :
    U.toScheme ⟶ ProjectiveLine.scheme (ULift.{u} ℤ) :=
  affineMap X U s ≫
    (ProjectiveSpace.CoordinateChart.iso (R := ULift.{u} ℤ) 1 0).inv ≫
    (ProjectiveLine.chartX (ULift.{u} ℤ)).ι

/-- The integral projective-line section is the explicit composite through the `X`-chart. -/
theorem integralSection_def :
    integralSection X U s =
      affineMap X U s ≫
        (ProjectiveSpace.CoordinateChart.iso (R := ULift.{u} ℤ) 1 0).inv ≫
        (ProjectiveLine.chartX (ULift.{u} ℤ)).ι := sorry

/-- The morphism from `U` to the relative projective line whose affine coordinate is `s`. -/
noncomputable def sectionMap : U.toScheme ⟶ ProjectiveSpace 1 S :=
  pullback.lift (U.ι ≫ X.hom)
    (integralSection X U s) (Subsingleton.elim _ _)

/-- The projective-line section lies over the original structure map to `S`. -/
theorem sectionMap_toBase :
    sectionMap X U s ≫ ProjectiveSpace.toBase 1 S = U.ι ≫ X.hom := sorry

/-- The graph of `s`, as a morphism into `X ×ₛ ℙ¹ₛ`. -/
noncomputable def graph :
    U.toScheme ⟶ pullback X.hom (ProjectiveSpace.toBase 1 S) :=
  pullback.lift U.ι (sectionMap X U s) (sectionMap_toBase X U s).symm

/-- The first projection of the graph is the open immersion `U.ι`. -/
theorem graph_fst :
    graph X U s ≫ pullback.fst X.hom (ProjectiveSpace.toBase 1 S) = U.ι := sorry

/-- The second projection of the graph is `sectionMap X U s`. -/
theorem graph_snd :
    graph X U s ≫ pullback.snd X.hom (ProjectiveSpace.toBase 1 S) =
      sectionMap X U s := sorry

/-- The scheme-theoretic closure of the graph of `s` in `X ×ₛ ℙ¹ₛ`. -/
abbrev closure : Scheme.{u} := (graph X U s).image

/-- The projection `p : Y ⟶ X` from the graph closure. -/
noncomputable def fst : closure X U s ⟶ X.left :=
  (graph X U s).imageι ≫ pullback.fst X.hom (ProjectiveSpace.toBase 1 S)

/-- The first projection is induced by the first projection of `X ×ₛ ℙ¹ₛ`. -/
theorem fst_def :
    fst X U s =
      (graph X U s).imageι ≫ pullback.fst X.hom (ProjectiveSpace.toBase 1 S) := sorry

/-- The projection `q : Y ⟶ ℙ¹ₛ` from the graph closure. -/
noncomputable def snd : closure X U s ⟶ ProjectiveSpace 1 S :=
  (graph X U s).imageι ≫ pullback.snd X.hom (ProjectiveSpace.toBase 1 S)

/-- The second projection is induced by the second projection of `X ×ₛ ℙ¹ₛ`. -/
theorem snd_def :
    snd X U s =
      (graph X U s).imageι ≫ pullback.snd X.hom (ProjectiveSpace.toBase 1 S) := sorry

/-- The graph closure of an invertible section on a nonempty open of an integral scheme is
integral. -/
instance instIsIntegralClosure [IsIntegral X.left] [Nonempty U] :
    IsIntegral (closure X U s) := sorry

/-- The projection from the graph closure to `X` is proper. -/
instance instIsProperFst : IsProper (fst X U s) := sorry

/-- The projection from the graph closure to an integral `X` is dominant. -/
instance instIsDominantFst [IsIntegral X.left] [Nonempty U] :
    IsDominant (fst X U s) := sorry

/-- The graph closure is locally of finite type over `S` when `X` is. -/
instance instLocallyOfFiniteTypeClosure [LocallyOfFiniteType X.hom] :
    LocallyOfFiniteType (fst X U s ≫ X.hom) := sorry

/-- Over the open on which `s` is defined, the graph-closure projection is an isomorphism. -/
instance instIsIsoRestrictFst
    [UniversallyCatenary S] [LocallyOfFiniteType X.hom] [IsIntegral X.left]
    [Nonempty U] : IsIso (fst X U s ∣_ U) := sorry

/-- The pullback of `f` from `X` to the function field of the graph closure. -/
noncomputable def function [IsIntegral X.left] [Nonempty U]
    (f : X.left.functionFieldˣ) : (closure X U s).functionFieldˣ :=
  (fst X U s).functionFieldUnitsMap
    (fst X U s).map_genericPoint_eq_of_isDominant f

/-- The rational function on the graph closure is induced by the first projection. -/
theorem function_def [IsIntegral X.left] [Nonempty U]
    (f : X.left.functionFieldˣ) :
    function X U s f =
      (fst X U s).functionFieldUnitsMap
        (fst X U s).map_genericPoint_eq_of_isDominant f := sorry

/-- The pullback `Y₀ = q⁻¹D₀` on the graph closure. -/
noncomputable def zeroDivisor : (closure X U s).IdealSheafData :=
  (ProjectiveLine.Relative.zeroDivisor S).comap (snd X U s)

/-- The zero divisor is the ideal-sheaf pullback of `D₀`. -/
theorem zeroDivisor_def :
    zeroDivisor X U s =
      (ProjectiveLine.Relative.zeroDivisor S).comap (snd X U s) := sorry

/-- The pullback `Y∞ = q⁻¹D∞` on the graph closure. -/
noncomputable def infinityDivisor : (closure X U s).IdealSheafData :=
  (ProjectiveLine.Relative.infinityDivisor S).comap (snd X U s)

/-- The infinity divisor is the ideal-sheaf pullback of `D∞`. -/
theorem infinityDivisor_def :
    infinityDivisor X U s =
      (ProjectiveLine.Relative.infinityDivisor S).comap (snd X U s) := sorry

/-- The pullback of `D₀` along the second graph-closure projection is defined. -/
instance instIsEffectiveCartierZeroDivisor
    [IsIntegral X.left] [Nonempty U] :
    IsEffectiveCartierDivisor (zeroDivisor X U s).subschemeι := sorry

/-- The pullback of `D∞` along the second graph-closure projection is defined. -/
instance instIsEffectiveCartierInfinityDivisor
    [IsIntegral X.left] [Nonempty U] :
    IsEffectiveCartierDivisor (infinityDivisor X U s).subschemeι := sorry

/-- The zero divisor viewed as its scheme-theoretic image in `X`. -/
noncomputable def zeroImage : X.left.IdealSheafData :=
  ((zeroDivisor X U s).subschemeι ≫ fst X U s).ker

/-- The zero image is the kernel ideal of its composite map to `X`. -/
theorem zeroImage_def :
    zeroImage X U s = ((zeroDivisor X U s).subschemeι ≫ fst X U s).ker := sorry

/-- The infinity divisor viewed as its scheme-theoretic image in `X`. -/
noncomputable def infinityImage : X.left.IdealSheafData :=
  ((infinityDivisor X U s).subschemeι ≫ fst X U s).ker

/-- The infinity image is the kernel ideal of its composite map to `X`. -/
theorem infinityImage_def :
    infinityImage X U s =
      ((infinityDivisor X U s).subschemeι ≫ fst X U s).ker := sorry

/-- The zero divisor maps to `X` as a closed immersion. -/
instance instIsClosedImmersionZeroToSource :
    IsClosedImmersion ((zeroDivisor X U s).subschemeι ≫ fst X U s) := sorry

/-- The infinity divisor maps to `X` as a closed immersion. -/
instance instIsClosedImmersionInfinityToSource :
    IsClosedImmersion ((infinityDivisor X U s).subschemeι ≫ fst X U s) := sorry

end AlgebraicGeometry.RationalFunctionGraph
