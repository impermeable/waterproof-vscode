import React from "react";
import { createRoot } from "react-dom/client";

import "../styles/index";
// get the react panel
import Tactics from "./tactics";

const data = window.extraData;

const container = document.getElementById("root");
// createRoot(container!) if you use TypeScript
const root = createRoot(container!);
// render the tactics panel
root.render(
    <React.StrictMode>
        <Tactics data={data} />
    </React.StrictMode>
);
