import React from "react";
import { createRoot } from "react-dom/client";

import "../styles/index.css";
// get the react panel
import CommonExecute from "./commonExecute";

const container = document.getElementById("root");
// createRoot(container!) if you use TypeScript
const root = createRoot(container!); 
//render the common execute panel
root.render(
  <React.StrictMode>
    <CommonExecute/>
  </React.StrictMode>
);