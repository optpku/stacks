module

public import ReasLib.AlgebraicGeometry.GroupoidScheme

/-!
# Morphisms of groupoid schemes

This module records the condition that a morphism of groupoid schemes is the identity on
objects relative to a specified equality of their object schemes.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.GroupoidScheme.Hom

/-- A groupoid-scheme morphism is identity on objects relative to `hU` when its object
component is the equality-induced morphism. -/
def IsIdentityOnObjects {S : Scheme.{u}} {G H : GroupoidScheme S}
    (f : Hom G H) (hU : G.U = H.U) : Prop :=
  f.obj = eqToHom hU

/-- A morphism is identity on objects relative to `hU` if and only if its object component
is the morphism induced by `hU`. -/
theorem isIdentityOnObjects_iff {S : Scheme.{u}} {G H : GroupoidScheme S}
    (f : Hom G H) (hU : G.U = H.U) :
    f.IsIdentityOnObjects hU ↔ f.obj = eqToHom hU := sorry

namespace IsIdentityOnObjects

/-- An identity-on-objects morphism commutes with the source maps. -/
theorem source {S : Scheme.{u}} {G H : GroupoidScheme S} {f : Hom G H}
    {hU : G.U = H.U} (hf : f.IsIdentityOnObjects hU) :
    f.arrow ≫ H.s = G.s ≫ eqToHom hU := sorry

/-- An identity-on-objects morphism commutes with the target maps. -/
theorem target {S : Scheme.{u}} {G H : GroupoidScheme S} {f : Hom G H}
    {hU : G.U = H.U} (hf : f.IsIdentityOnObjects hU) :
    f.arrow ≫ H.t = G.t ≫ eqToHom hU := sorry

/-- An identity-on-objects morphism commutes with groupoid composition. -/
theorem map_c {S : Scheme.{u}} {G H : GroupoidScheme S} {f : Hom G H}
    {hU : G.U = H.U} (hf : f.IsIdentityOnObjects hU) :
    G.c ≫ f.arrow = f.composableMap ≫ H.c := sorry

/-- The identity morphism is identity on objects. -/
theorem id {S : Scheme.{u}} (G : GroupoidScheme S) :
    (Hom.id G).IsIdentityOnObjects rfl := sorry

/-- A composite of identity-on-objects morphisms is identity on objects. -/
theorem comp {S : Scheme.{u}} {G H K : GroupoidScheme S} {f : Hom G H} {g : Hom H K}
    {hGH : G.U = H.U} {hHK : H.U = K.U}
    (hf : f.IsIdentityOnObjects hGH) (hg : g.IsIdentityOnObjects hHK) :
    (Hom.comp f g).IsIdentityOnObjects (hGH.trans hHK) := sorry

end IsIdentityOnObjects

end AlgebraicGeometry.GroupoidScheme.Hom
