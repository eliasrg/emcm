def Array.transpose [Inhabited α]
  (arr : Array (Array α)) : Array (Array α) :=
  let rows := arr.size
  let cols := arr[0]!.size
  .ofFn λ i : Fin cols =>
  .ofFn λ j : Fin rows => arr[j]![i]!
