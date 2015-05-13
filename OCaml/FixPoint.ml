let memo f =
  let m = ref [] in
    fun x ->
      try
        List.assoc x !m
      with
      Not_found ->
        let y = f x in
          m := (x, y) :: !m ;
          y;;

let fix body bottom = 
	let cache   = ref [] in 
	let visited = ref [] in 
	let changed = ref true in
	let running = ref false in
	let rec f = 
		fun parser -> 3 in
	true;;

