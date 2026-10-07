module

public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap67.Definition_67_48_3_IntegralClosure
public import stacks_project.Chap67.Definition_67_48_3_RelativeSpectrum

/-!
# Canonical factorization through the relative spectrum of `f_* 𝒪_X`

A qcqs morphism `f : X ⟶ Y` of algebraic spaces factors as
`X ⟶ relativeSpec (pushforwardStructureQcAlgebra f) ⟶ Y`, classified by the
canonical algebra map `f_* 𝒪_X ⟶ (t ≫ f)_* 𝒪_T` on test objects.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Evaluation of `f_* 𝒪_X` at a test map `t : T ⟶ X`, as a morphism of `𝒪_Y`-algebras
into `(t ≫ f)_* 𝒪_T`. -/
def Hom.toPushforwardRelativeSpecAlgebraMap {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] {T : Over S} (t : ofOver T ⟶ X) :
    (pushforwardStructureQcAlgebra f).obj ⟶ relativeSpectrumTarget (t ≫ f) :=
  Under.homMk
    ((commRingPushforward f).map (commRingStructureSheafMap t) ≫
      commRingPushforwardPrecomp t f)
    sorry

/-- The underlying sheaf morphism of `toPushforwardRelativeSpecAlgebraMap f t` is the
pushforward of `t^♯` followed by the Kan-counit comparison. -/
theorem Hom.toPushforwardRelativeSpecAlgebraMap_right {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] {T : Over S} (t : ofOver T ⟶ X) :
    (Hom.toPushforwardRelativeSpecAlgebraMap f t).right =
      (commRingPushforward f).map (commRingStructureSheafMap t) ≫
        commRingPushforwardPrecomp t f :=
  sorry

/-- The canonical first-factor morphism `X ⟶ relativeSpec (f_* 𝒪_X)` of a qcqs
morphism. -/
def Hom.toPushforwardRelativeSpec {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] :
    X ⟶ relativeSpec (pushforwardStructureQcAlgebra f) where
  app T :=
    TypeCat.ofHom fun (x : X.functorOfPoints.obj T) ↦
      relativeSpectrumPairMk (yonedaEquiv.symm x ≫ f)
        (Hom.toPushforwardRelativeSpecAlgebraMap f (yonedaEquiv.symm x))
  naturality := sorry

/-- The component of `toPushforwardRelativeSpec f` at `T` has underlying map to `Y`
equal to `f`. -/
theorem Hom.toPushforwardRelativeSpec_app_toX {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] (T : (Over S)ᵒᵖ)
    (x : X.functorOfPoints.obj T) :
    ((Hom.toPushforwardRelativeSpec f).app T x).1 =
      yonedaEquiv ((yonedaEquiv.symm x ≫ f : yoneda.obj T.unop ⟶ Y.functorOfPoints)) :=
  sorry

/-- The canonical factorization identity
`toPushforwardRelativeSpec f ≫ relativeSpecπ (pushforwardStructureQcAlgebra f) = f`. -/
theorem Hom.toPushforwardRelativeSpec_comp_relativeSpecπ {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] :
    Hom.toPushforwardRelativeSpec f ≫
        relativeSpecπ (pushforwardStructureQcAlgebra f) =
      f :=
  sorry

/-- The section `X ⟶ X ×_Y relativeSpec (f_* 𝒪_X)` over `X` classified by the
canonical first-factor morphism. -/
def Hom.toPushforwardRelativeSpecOver {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] :
    X ⟶ pullback f (relativeSpecπ (pushforwardStructureQcAlgebra f)) :=
  pullback.lift (𝟙 X) (Hom.toPushforwardRelativeSpec f) sorry

/-- The section `toPushforwardRelativeSpecOver f` projects to `𝟙 X` on the first
factor. -/
theorem Hom.toPushforwardRelativeSpecOver_fst {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] :
    Hom.toPushforwardRelativeSpecOver f ≫
        pullback.fst f (relativeSpecπ (pushforwardStructureQcAlgebra f)) =
      𝟙 X :=
  sorry

/-- The section `toPushforwardRelativeSpecOver f` projects to
`toPushforwardRelativeSpec f` on the second factor. -/
theorem Hom.toPushforwardRelativeSpecOver_snd {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] :
    Hom.toPushforwardRelativeSpecOver f ≫
        pullback.snd f (relativeSpecπ (pushforwardStructureQcAlgebra f)) =
      Hom.toPushforwardRelativeSpec f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
