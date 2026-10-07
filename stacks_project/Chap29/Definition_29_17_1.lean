module

public import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary
import StacksCheckRecall

universe u

/- Definition 29.17.1: a locally Noetherian scheme `S` is universally catenary if every scheme
locally of finite type over `S` is catenary. -/
@[stacks 02J8] #check (AlgebraicGeometry.UniversallyCatenary :
  AlgebraicGeometry.Scheme.{u} → Prop)
