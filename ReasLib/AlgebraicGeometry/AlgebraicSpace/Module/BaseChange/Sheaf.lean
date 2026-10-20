module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sites.Fpqc
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.BaseChange.IsomorphismFunctor

/-!
# Fpqc sheafness of flattening functors on schemes over an algebraic space

The isomorphism functor of a morphism of quasicoherent modules on an algebraic
space is an fpqc sheaf. Any subterminal functor on schemes over the base that
detects injectivity, surjectivity, or vanishing of the base-changed morphism
is also an fpqc sheaf.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
variable {ℱ 𝒢 : X.Modules} [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent]

/-- The functor detecting when a morphism of quasi-coherent modules becomes an
isomorphism after base change to a scheme over `B` is an fpqc sheaf. -/
theorem isomorphismFunctor_isSheaf_fpqc (u : ℱ ⟶ 𝒢) :
    Presheaf.IsSheaf (SchemeOver.fpqcTopology B) (isomorphismFunctor f u) :=
  sorry

/-- A subterminal functor detecting when base changes of a morphism of
quasi-coherent modules are monomorphisms is an fpqc sheaf on `SchemeOver B`. -/
theorem injectivityFunctor_isSheaf_fpqc (u : ℱ ⟶ 𝒢)
    (F_inj : (SchemeOver B)ᵒᵖ ⥤ Type u)
    [hF_subterminal : ∀ T : SchemeOver B, Subsingleton (F_inj.obj (op T))]
    (hF_inj : ∀ T : SchemeOver B,
      Nonempty (F_inj.obj (op T)) ↔ Mono (baseChangeMap f T.hom u)) :
    Presheaf.IsSheaf (SchemeOver.fpqcTopology B) F_inj :=
  sorry

/-- A subterminal functor detecting when base changes of a morphism of
quasi-coherent modules are epimorphisms is an fpqc sheaf on `SchemeOver B`. -/
theorem surjectivityFunctor_isSheaf_fpqc (u : ℱ ⟶ 𝒢)
    (F_surj : (SchemeOver B)ᵒᵖ ⥤ Type u)
    [hF_subterminal : ∀ T : SchemeOver B, Subsingleton (F_surj.obj (op T))]
    (hF_surj : ∀ T : SchemeOver B,
      Nonempty (F_surj.obj (op T)) ↔ Epi (baseChangeMap f T.hom u)) :
    Presheaf.IsSheaf (SchemeOver.fpqcTopology B) F_surj :=
  sorry

/-- A subterminal functor detecting when base changes of a morphism of
quasi-coherent modules vanish is an fpqc sheaf on `SchemeOver B`. -/
theorem zeroFunctor_isSheaf_fpqc (u : ℱ ⟶ 𝒢)
    (F_zero : (SchemeOver B)ᵒᵖ ⥤ Type u)
    [hF_subterminal : ∀ T : SchemeOver B, Subsingleton (F_zero.obj (op T))]
    (hF_zero : ∀ T : SchemeOver B,
      Nonempty (F_zero.obj (op T)) ↔ baseChangeMap f T.hom u = 0) :
    Presheaf.IsSheaf (SchemeOver.fpqcTopology B) F_zero :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
