/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.DeRham.Map
import StacksCheckRecall

@[expose] public section

/- Definition 17.30.4 (0FKQ) (1): for a morphism `h : X ⟶ S` of ringed spaces,
`Ωᵈᴿ[h]` is the relative de Rham complex of `𝒪_X` over `h⁻¹𝒪_S`. -/
@[stacks 0FKQ "(1)"]
#check @AlgebraicGeometry.RingedSpace.DeRham.complex
#check @AlgebraicGeometry.RingedSpace.DeRham.complex_X
#check @AlgebraicGeometry.RingedSpace.DeRham.complex_d
#check @AlgebraicGeometry.RingedSpace.DeRham.d_sq

/- Definition 17.30.4 (0FKQ) (2): a commutative square of ringed spaces induces the canonical
map `Ωᵈᴿ[h] ⟶ f_* Ωᵈᴿ[h']`. -/
@[stacks 0FKQ "(2)"]
#check @AlgebraicGeometry.RingedSpace.DeRham.map

-- The reusable lower layers retain the identity and horizontal-composition laws, including
-- the canonical coherence isomorphisms for successive restrictions of scalars.
#check @CommRingCat.DeRham.map_f
#check @CommRingCat.DeRham.FormRestriction.mapApp_comp
#check @CommRingCat.DeRham.Restriction.map_comp
#check @PresheafOfModules.DeRham.mapApp_app
#check @PresheafOfModules.DeRham.map_id
#check @PresheafOfModules.DeRham.map_comp
#check @SheafOfModules.RingedSite.DeRham.map_id
#check @SheafOfModules.RingedSite.DeRham.map_comp

-- The ringed-space construction exposes its adjunction and degreewise specifications.
#check @AlgebraicGeometry.RingedSpace.DeRham.baseChangeMap_adj
#check @AlgebraicGeometry.RingedSpace.DeRham.fixedMap_f
#check @AlgebraicGeometry.RingedSpace.DeRham.map_f
