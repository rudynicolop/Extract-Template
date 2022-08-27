module V = Vic.Victor

let rec list_of_vic : 'a V.vic -> 'a list =
function
| V.Coq_vnil -> []
| V.Coq_vcons (_,a,v) -> a :: list_of_vic v
