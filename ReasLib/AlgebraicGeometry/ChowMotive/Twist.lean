module

public import ReasLib.AlgebraicGeometry.ChowMotive
public import ReasLib.AlgebraicGeometry.Correspondence.GradedCategory.Linear

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace ChowMotive

variable {k : Type u} [Field k]

/-- Simultaneously shifting two Tate indices preserves their difference. -/
theorem twistDegree (a b n : ℤ) : b - a = (b + n) - (a + n) := by
  omega

/-- Shift the Tate index of a motive, retaining its scheme and projector. -/
def twist (M : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k)) (n : ℤ) :
    ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) where
  X := (M.X.1, M.X.2 + n)
  p := Correspondence.castDegree (twistDegree M.X.2 M.X.2 n) M.p
  idem := sorry

/-- Twisting adds to the underlying Tate index. -/
theorem twist_index (M : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k)) (n : ℤ) :
    (twist M n).X.2 = M.X.2 + n := rfl

/-- Twist a morphism by transporting its correspondence degree. -/
def twistHom {M N : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k)}
    (f : M ⟶ N) (n : ℤ) : twist M n ⟶ twist N n where
  f := Correspondence.castDegree (twistDegree M.X.2 N.X.2 n) f.f
  comm := sorry

/-- The underlying correspondence of a twisted morphism is its degree transport. -/
theorem twistHom_f {M N : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k)}
    (f : M ⟶ N) (n : ℤ) :
    (twistHom f n).f =
      Correspondence.castDegree (twistDegree M.X.2 N.X.2 n) f.f := rfl

/-- The Tate-twist functor on arbitrary Chow motives. -/
def twistFunctor (k : Type u) [Field k] (n : ℤ) :
    ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) where
  obj M := twist M n
  map f := twistHom f n
  map_id := sorry
  map_comp := sorry

end ChowMotive
