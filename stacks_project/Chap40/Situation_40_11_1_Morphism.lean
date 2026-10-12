/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Morphism

/-!
# Identity-on-objects morphisms of groupoid schemes

This compatibility module exposes the shared identity-on-objects API to chapter-level
consumers.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.GroupoidScheme.Hom

/- The shared owner defines the identity-on-objects predicate. -/
#check
  (AlgebraicGeometry.GroupoidScheme.Hom.IsIdentityOnObjects :
    {S : Scheme.{u}} → {G H : GroupoidScheme S} → Hom G H → G.U = H.U → Prop)

/- The shared owner exposes the defining equation of the predicate. -/
#check
  (AlgebraicGeometry.GroupoidScheme.Hom.isIdentityOnObjects_iff :
    ∀ {S : Scheme.{u}} {G H : GroupoidScheme S} (f : Hom G H) (hU : G.U = H.U),
      f.IsIdentityOnObjects hU ↔ f.obj = eqToHom hU)

/- The shared owner exposes compatibility with source maps. -/
#check
  (AlgebraicGeometry.GroupoidScheme.Hom.IsIdentityOnObjects.source :
    ∀ {S : Scheme.{u}} {G H : GroupoidScheme S} {f : Hom G H}
      {hU : G.U = H.U}, f.IsIdentityOnObjects hU →
        f.arrow ≫ H.s = G.s ≫ eqToHom hU)

/- The shared owner exposes compatibility with target maps. -/
#check
  (AlgebraicGeometry.GroupoidScheme.Hom.IsIdentityOnObjects.target :
    ∀ {S : Scheme.{u}} {G H : GroupoidScheme S} {f : Hom G H}
      {hU : G.U = H.U}, f.IsIdentityOnObjects hU →
        f.arrow ≫ H.t = G.t ≫ eqToHom hU)

/- The shared owner exposes compatibility with groupoid composition. -/
#check
  (AlgebraicGeometry.GroupoidScheme.Hom.IsIdentityOnObjects.map_c :
    ∀ {S : Scheme.{u}} {G H : GroupoidScheme S} {f : Hom G H}
      {hU : G.U = H.U}, f.IsIdentityOnObjects hU →
        G.c ≫ f.arrow = f.composableMap ≫ H.c)

/- The shared predicate holds for identity morphisms. -/
#check
  (AlgebraicGeometry.GroupoidScheme.Hom.IsIdentityOnObjects.id :
    ∀ {S : Scheme.{u}} (G : GroupoidScheme S),
      (Hom.id G).IsIdentityOnObjects rfl)

/- The shared predicate is closed under composition. -/
#check
  (AlgebraicGeometry.GroupoidScheme.Hom.IsIdentityOnObjects.comp :
    ∀ {S : Scheme.{u}} {G H K : GroupoidScheme S} {f : Hom G H} {g : Hom H K}
      {hGH : G.U = H.U} {hHK : H.U = K.U},
      f.IsIdentityOnObjects hGH → g.IsIdentityOnObjects hHK →
        (Hom.comp f g).IsIdentityOnObjects (hGH.trans hHK))

end AlgebraicGeometry.GroupoidScheme.Hom
