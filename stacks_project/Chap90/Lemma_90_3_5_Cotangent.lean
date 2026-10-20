/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.LocalRing.Cotangent.Map
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.Cotangent

/-!
# Cotangent and relative-cotangent maps along morphisms in `C_Λ`

Local algebra homomorphisms induce maps of cotangent spaces. In the base category
`ArtinianLocalAlgCat Λ k`, they also induce maps of the relative quotients
`maximalIdeal ⧸ (m_Λ · (-) + maximalIdeal ^ 2)`, where `m_Λ` is
`RingHom.ker (algebraMap Λ k)`.
-/

@[expose] public section

open IsLocalRing

universe u v w

#check (IsLocalRing.CotangentSpace.mapAlgHom :
  ∀ {R : Type u} {A : Type v} {B : Type w} [CommRing R] [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [Algebra R A] [Algebra R B]
    (f : A →ₐ[R] B) [IsLocalHom f], CotangentSpace A →ₗ[R] CotangentSpace B)

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

#check (ArtinianLocalAlgCat.Hom.mapRelative :
  ∀ {A B : ArtinianLocalAlgCat Λ k} (f : ArtinianLocalAlgCat.Hom A B),
    (maximalIdeal A.carrier ⧸ ArtinianLocalAlgCat.relativeSubmodule A) →ₗ[Λ]
      (maximalIdeal B.carrier ⧸ ArtinianLocalAlgCat.relativeSubmodule B))
