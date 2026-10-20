module

public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap67.Definition_67_48_3_IntegralClosure
public import stacks_project.Chap67.Definition_67_48_3_RelativeSpectrum
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeSpectrum.Factorization

/-!
# Canonical relative-spectrum factorization

The canonical factorization and pullback section are provided by the shared
relative-spectrum API.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

universe u

#check
  (AlgebraicGeometry.AlgebraicSpace.Hom.toPushforwardRelativeSpec :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f],
    X ⟶ relativeSpec (pushforwardStructureQcAlgebra f))

#check
  (AlgebraicGeometry.AlgebraicSpace.Hom.toPushforwardRelativeSpec_app_toX :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] (T : (Over S)ᵒᵖ)
    (x : X.functorOfPoints.obj T),
    ((Hom.toPushforwardRelativeSpec f).app T x).1 =
      yonedaEquiv ((yonedaEquiv.symm x ≫ f : yoneda.obj T.unop ⟶ Y.functorOfPoints)))

#check
  (AlgebraicGeometry.AlgebraicSpace.Hom.toPushforwardRelativeSpec_comp_relativeSpecπ :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f],
    Hom.toPushforwardRelativeSpec f ≫
        relativeSpecπ (pushforwardStructureQcAlgebra f) =
      f)

#check
  (AlgebraicGeometry.AlgebraicSpace.Hom.toPushforwardRelativeSpecOver :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f],
    X ⟶ pullback f (relativeSpecπ (pushforwardStructureQcAlgebra f)))

#check
  (AlgebraicGeometry.AlgebraicSpace.Hom.toPushforwardRelativeSpecOver_fst :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f],
    Hom.toPushforwardRelativeSpecOver f ≫
        pullback.fst f (relativeSpecπ (pushforwardStructureQcAlgebra f)) =
      𝟙 X)

#check
  (AlgebraicGeometry.AlgebraicSpace.Hom.toPushforwardRelativeSpecOver_snd :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f],
    Hom.toPushforwardRelativeSpecOver f ≫
        pullback.snd f (relativeSpecπ (pushforwardStructureQcAlgebra f)) =
      Hom.toPushforwardRelativeSpec f)
