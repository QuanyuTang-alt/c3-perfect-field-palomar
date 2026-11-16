module

public import C3Integration

@[expose] public section
namespace PalomarC3
universe u
/-- A perfect-field representation-infinite finite-dimensional algebra has
infinitely many connected components in its actual Auslander--Reiten graph. -/
theorem main_result (k A : Type u) [Field k] [Ring A] [Algebra k A]
    [PerfectField k] [FiniteDimensional k A]
    (hA : C3PerfectField.InfiniteRepresentationType k A) :
    Infinite (C3PerfectField.ARGraph k A).ConnectedComponent :=
  C3PerfectField.mainTheorem k A hA
end PalomarC3
