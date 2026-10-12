/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.BaseChange.IsomorphismFunctor
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Sheaf

/-!
# Sheaf conditions for base-change properties of module morphisms

This module records fpqc descent for subterminal functors detecting properties
of base-changed morphisms of quasicoherent scheme modules.
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X S : Scheme.{u}} (f : X ⟶ S)
variable {ℱ 𝒢 : X.Modules} [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent]

/-- The functor detecting when a morphism of quasicoherent modules becomes an
isomorphism after base change is an fpqc sheaf. -/
theorem isomorphismFunctor_isSheaf_fpqc (u : ℱ ⟶ 𝒢) :
    Presheaf.IsSheaf (Scheme.fpqcTopology.over S) (isomorphismFunctor f u) := sorry

/-- A subterminal functor detecting when base changes of a morphism of
quasicoherent modules are monomorphisms is an fpqc sheaf. -/
theorem injectivityFunctor_isSheaf_fpqc (u : ℱ ⟶ 𝒢)
    (F_inj : (Over S)ᵒᵖ ⥤ Type u)
    [hF_subterminal : ∀ T : Over S, Subsingleton (F_inj.obj (op T))]
    (hF_inj : ∀ T : Over S,
      Nonempty (F_inj.obj (op T)) ↔ Mono (baseChangeMap f T.hom u)) :
    Presheaf.IsSheaf (Scheme.fpqcTopology.over S) F_inj := sorry

/-- A subterminal functor detecting when base changes of a morphism of
quasicoherent modules are epimorphisms is an fpqc sheaf. -/
theorem surjectivityFunctor_isSheaf_fpqc (u : ℱ ⟶ 𝒢)
    (F_surj : (Over S)ᵒᵖ ⥤ Type u)
    [hF_subterminal : ∀ T : Over S, Subsingleton (F_surj.obj (op T))]
    (hF_surj : ∀ T : Over S,
      Nonempty (F_surj.obj (op T)) ↔ Epi (baseChangeMap f T.hom u)) :
    Presheaf.IsSheaf (Scheme.fpqcTopology.over S) F_surj := sorry

/-- A subterminal functor detecting when base changes of a morphism of
quasicoherent modules vanish is an fpqc sheaf. -/
theorem zeroFunctor_isSheaf_fpqc (u : ℱ ⟶ 𝒢)
    (F_zero : (Over S)ᵒᵖ ⥤ Type u)
    [hF_subterminal : ∀ T : Over S, Subsingleton (F_zero.obj (op T))]
    (hF_zero : ∀ T : Over S,
      Nonempty (F_zero.obj (op T)) ↔ baseChangeMap f T.hom u = 0) :
    Presheaf.IsSheaf (Scheme.fpqcTopology.over S) F_zero := sorry

end AlgebraicGeometry.Scheme.Modules
