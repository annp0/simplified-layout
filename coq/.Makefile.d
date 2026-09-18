Floors.vo Floors.glob Floors.v.beautified Floors.required_vo: Floors.v 
Floors.vio: Floors.v 
Floors.vos Floors.vok Floors.required_vos: Floors.v 
Chain.vo Chain.glob Chain.v.beautified Chain.required_vo: Chain.v Floors.vo
Chain.vio: Chain.v Floors.vio
Chain.vos Chain.vok Chain.required_vos: Chain.v Floors.vos
Recognize.vo Recognize.glob Recognize.v.beautified Recognize.required_vo: Recognize.v Floors.vo Chain.vo
Recognize.vio: Recognize.v Floors.vio Chain.vio
Recognize.vos Recognize.vok Recognize.required_vos: Recognize.v Floors.vos Chain.vos
Shape.vo Shape.glob Shape.v.beautified Shape.required_vo: Shape.v Floors.vo Chain.vo Recognize.vo
Shape.vio: Shape.v Floors.vio Chain.vio Recognize.vio
Shape.vos Shape.vok Shape.required_vos: Shape.v Floors.vos Chain.vos Recognize.vos
Dense.vo Dense.glob Dense.v.beautified Dense.required_vo: Dense.v 
Dense.vio: Dense.v 
Dense.vos Dense.vok Dense.required_vos: Dense.v 
