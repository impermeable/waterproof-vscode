import React from "react";
import { createRoot } from "react-dom/client";

import "../styles/index.css";
// get the react panel
import ExpandDefinition from "./expandDefinition";

const container = document.getElementById("root");
// createRoot(container!) if you use TypeScript
const root = createRoot(container!); 
//render the expand definition panel
root.render(
  <React.StrictMode>
    <ExpandDefinition/>
  </React.StrictMode>
);
