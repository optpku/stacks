/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Properties
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Restriction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Open.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Open.SchemeTheoreticDensity
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.SmallEtale.Modules

/-- A finite-type quasicoherent module flat over a locally finitely presented morphism of
algebraic spaces is finitely presented if its restriction above a quasi-compact,
scheme-theoretically dense open subspace of the target is finitely presented. -/
theorem finitePresentation_of_restrict_of_flatOver
    {S : Scheme.{u}} {X Y V : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] (F : Modules X)
    (h_quasicoherent : IsQuasicoherent F) (h_finiteType : IsFiniteType F)
    (h_flat : FlatOver F f) (ι : V ⟶ Y)
    (h_open : Representable.IsOpenImmersion ι) (h_quasiCompact : Representable.QuasiCompact ι)
    (h_dense : Open.IsSchemeTheoreticallyDense ι)
    (h_restrict : IsFinitePresentation
      ((restrict (Open.inverseImageι f ι h_open)
        (Representable.isOpenImmersion_etale (Open.inverseImageι f ι h_open)
          (Open.inverseImage_isOpenImmersion f ι h_open))).obj F)) :
    IsFinitePresentation F := sorry

end AlgebraicGeometry.AlgebraicSpace.SmallEtale.Modules
