/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import ReasLib.Topology.Sheaves.Glue

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

-- Local declaration justification (metaprogramming implementation): Lean's module system
-- must expose the private cover body to the public extension construction.
set_option backward.privateInPublic true in
/-- The two-open cover consisting of `V` and `W`. -/
private def extensionCover {X : Scheme.{u}} (V W : X.Opens) : Bool → X.Opens
  | true => V
  | false => W

-- Local declaration justification (metaprogramming implementation): Lean's module system
-- must expose the private covering law to the public extension construction.
set_option backward.privateInPublic true in
/-- The two-open cover covers the whole space when `V ⊔ W = ⊤`. -/
private theorem extensionCover_covers {X : Scheme.{u}} {V W : X.Opens}
    (hcover : V ⊔ W = ⊤) : (⊤ : X.Opens) ≤ ⨆ i, extensionCover V W i := sorry

-- Local declaration justification (metaprogramming implementation): Lean's module system
-- must expose the private family body to the public extension construction.
set_option backward.privateInPublic true in
/-- The family formed by a section on `V` and the zero section on `W`. -/
private def extensionFamily {X : Scheme.{u}} {F : X.Modules} {V W : X.Opens}
    (s : Γ(F, V)) : ∀ i, Γ(F, extensionCover V W i)
  | true => s
  | false => 0

-- Local declaration justification (metaprogramming implementation): Lean's module system
-- must expose the private compatibility law to the public extension construction.
set_option backward.privateInPublic true in
/-- The section-and-zero family is compatible when sections over `W` vanish. -/
private theorem extensionFamily_compatible {X : Scheme.{u}} {F : X.Modules}
    {V W : X.Opens} (s : Γ(F, V))
    (hzero : ∀ U, U ≤ W → ∀ z : Γ(F, U), z = 0) :
    TopCat.Presheaf.IsCompatible
      (⟨F.presheaf, F.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat X).obj
      (extensionCover V W) (extensionFamily s) := sorry

-- Local declaration justification (metaprogramming implementation): Lean's exposed public
-- construction needs access to the private cover, local family, and compatibility laws.
set_option backward.privateInPublic true in
/-- The section obtained by extending a section over `V` by zero across `W`. -/
noncomputable def extendOfZeroOn {X : Scheme.{u}} (F : X.Modules)
    (V W : X.Opens) (hcover : V ⊔ W = ⊤)
    (hzero : ∀ U, U ≤ W → ∀ z : Γ(F, U), z = 0)
    (s : Γ(F, V)) : Γ(F, ⊤) :=
  TopCat.Sheaf.glueOfCompatibleFamily
    (⟨F.presheaf, F.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat X)
    (extensionCover V W) ⊤ (fun i => (extensionCover V W i).leTop)
    (extensionCover_covers hcover) (extensionFamily s)
    (extensionFamily_compatible s hzero)

/-- The zero extension restricts to the original section on `V` and to zero on `W`. -/
theorem extendOfZeroOn_spec {X : Scheme.{u}} (F : X.Modules)
    (V W : X.Opens) (hcover : V ⊔ W = ⊤)
    (hzero : ∀ U, U ≤ W → ∀ z : Γ(F, U), z = 0)
    (s : Γ(F, V)) :
    F.presheaf.map V.leTop.op (extendOfZeroOn F V W hcover hzero s) = s ∧
      F.presheaf.map W.leTop.op (extendOfZeroOn F V W hcover hzero s) = 0 := sorry

/-- When sections over `W` vanish, agreement with `s` on `V` determines the zero extension. -/
theorem extendOfZeroOn_unique {X : Scheme.{u}} (F : X.Modules)
    (V W : X.Opens) (hcover : V ⊔ W = ⊤)
    (hzero : ∀ U, U ≤ W → ∀ z : Γ(F, U), z = 0)
    (s : Γ(F, V)) (z : Γ(F, ⊤))
    (hzV : F.presheaf.map V.leTop.op z = s) :
    z = extendOfZeroOn F V W hcover hzero s := sorry

/-- Zero extension commutes with module morphisms whose source and target vanish on `W`. -/
theorem extendOfZeroOn_naturality {X : Scheme.{u}} {F G : X.Modules}
    (φ : F ⟶ G) (V W : X.Opens) (hcover : V ⊔ W = ⊤)
    (hzeroF : ∀ U, U ≤ W → ∀ z : Γ(F, U), z = 0)
    (hzeroG : ∀ U, U ≤ W → ∀ z : Γ(G, U), z = 0)
    (s : Γ(F, V)) :
    φ.app ⊤ (extendOfZeroOn F V W hcover hzeroF s) =
      extendOfZeroOn G V W hcover hzeroG (φ.app V s) := sorry

end AlgebraicGeometry.Scheme.Modules
